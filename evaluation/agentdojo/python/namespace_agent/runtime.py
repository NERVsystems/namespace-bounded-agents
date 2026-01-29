"""
P9Runtime - Python 9P client for executing filesystem operations.

This module provides a lightweight 9P client for communicating with the
AgentDojo 9P server. It handles connection management, namespace enforcement,
and operation execution.
"""

import socket
import struct
import logging
from dataclasses import dataclass
from typing import Optional

from .namespace import NamespaceSpec

logger = logging.getLogger(__name__)


# 9P protocol constants
NOTAG = 0xFFFF
NOFID = 0xFFFFFFFF

# 9P message types
Tversion = 100
Rversion = 101
Tauth = 102
Rauth = 103
Tattach = 104
Rattach = 105
Terror = 106  # illegal
Rerror = 107
Tflush = 108
Rflush = 109
Twalk = 110
Rwalk = 111
Topen = 112
Ropen = 113
Tcreate = 114
Rcreate = 115
Tread = 116
Rread = 117
Twrite = 118
Rwrite = 119
Tclunk = 120
Rclunk = 121
Tremove = 122
Rremove = 123
Tstat = 124
Rstat = 125
Twstat = 126
Rwstat = 127

# Open modes
OREAD = 0
OWRITE = 1
ORDWR = 2
OEXEC = 3
OTRUNC = 0x10


@dataclass
class P9ExecutionResult:
    """Result of a 9P filesystem operation."""

    success: bool
    data: Optional[str] = None
    error: Optional[str] = None
    path: Optional[str] = None
    blocked_by: Optional[str] = None  # "namespace", "server", or None


class P9Runtime:
    """
    9P client for executing filesystem operations.

    This client implements a minimal subset of the 9P protocol sufficient
    for tool invocation via query files.
    """

    def __init__(self, address: str, msize: int = 65536):
        """
        Initialize the 9P runtime.

        Args:
            address: Server address in "host:port" format
            msize: Maximum message size
        """
        self.address = address
        self.msize = msize
        self.sock: Optional[socket.socket] = None
        self.namespace: Optional[NamespaceSpec] = None
        self.tag_counter = 1
        self.fid_counter = 0
        self.root_fid = 0

    def connect(self):
        """Establish connection to the 9P server."""
        host, port = self.address.rsplit(":", 1)
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.sock.connect((host, int(port)))
        self.sock.settimeout(30.0)

        # Version handshake
        self._version()

        # Attach to root
        self._attach()

        logger.info(f"Connected to 9P server at {self.address}")

    def disconnect(self):
        """Close connection to the 9P server."""
        if self.sock:
            try:
                self.sock.close()
            except Exception:
                pass
            self.sock = None

    def set_namespace(self, namespace: NamespaceSpec):
        """Set the namespace for path validation."""
        self.namespace = namespace

    def read(self, path: str) -> P9ExecutionResult:
        """
        Read from a file path.

        Args:
            path: Absolute path to read from

        Returns:
            P9ExecutionResult with data or error
        """
        # Check namespace first
        if self.namespace and not self.namespace.contains(path):
            return P9ExecutionResult(
                success=False,
                error=f"path does not exist: {path}",
                path=path,
                blocked_by="namespace",
            )

        if not self.sock:
            return P9ExecutionResult(
                success=False,
                error="not connected",
                path=path,
            )

        try:
            # Walk to the file
            fid = self._next_fid()
            qid = self._walk(self.root_fid, fid, path)
            if qid is None:
                return P9ExecutionResult(
                    success=False,
                    error=f"path not found: {path}",
                    path=path,
                    blocked_by="server",
                )

            # Open for reading
            if not self._open(fid, OREAD):
                self._clunk(fid)
                return P9ExecutionResult(
                    success=False,
                    error=f"cannot open: {path}",
                    path=path,
                )

            # Read data
            data = self._read_all(fid)

            # Clunk
            self._clunk(fid)

            return P9ExecutionResult(
                success=True,
                data=data.decode("utf-8", errors="replace") if data else "",
                path=path,
            )

        except Exception as e:
            logger.error(f"Read error for {path}: {e}")
            return P9ExecutionResult(
                success=False,
                error=str(e),
                path=path,
            )

    def write(self, path: str, data: str) -> P9ExecutionResult:
        """
        Write to a file path.

        Args:
            path: Absolute path to write to
            data: Data to write

        Returns:
            P9ExecutionResult with success status
        """
        # Check namespace first
        if self.namespace and not self.namespace.contains(path):
            return P9ExecutionResult(
                success=False,
                error=f"path does not exist: {path}",
                path=path,
                blocked_by="namespace",
            )

        if not self.sock:
            return P9ExecutionResult(
                success=False,
                error="not connected",
                path=path,
            )

        try:
            # Walk to the file
            fid = self._next_fid()
            qid = self._walk(self.root_fid, fid, path)
            if qid is None:
                return P9ExecutionResult(
                    success=False,
                    error=f"path not found: {path}",
                    path=path,
                    blocked_by="server",
                )

            # Open for writing
            if not self._open(fid, OWRITE | OTRUNC):
                self._clunk(fid)
                return P9ExecutionResult(
                    success=False,
                    error=f"cannot open for write: {path}",
                    path=path,
                )

            # Write data
            data_bytes = data.encode("utf-8")
            written = self._write(fid, data_bytes)

            # Clunk
            self._clunk(fid)

            return P9ExecutionResult(
                success=True,
                data=f"wrote {written} bytes",
                path=path,
            )

        except Exception as e:
            logger.error(f"Write error for {path}: {e}")
            return P9ExecutionResult(
                success=False,
                error=str(e),
                path=path,
            )

    def _next_tag(self) -> int:
        """Get next message tag."""
        tag = self.tag_counter
        self.tag_counter = (self.tag_counter + 1) % 0xFFFE
        return tag

    def _next_fid(self) -> int:
        """Get next file ID."""
        self.fid_counter += 1
        return self.fid_counter

    def _send_recv(self, msg_type: int, payload: bytes) -> tuple[int, bytes]:
        """Send a message and receive response."""
        tag = self._next_tag()

        # Build message: size[4] type[1] tag[2] payload[...]
        header = struct.pack("<IBH", len(payload) + 7, msg_type, tag)
        self.sock.sendall(header + payload)

        # Receive response
        resp_header = self._recv_exact(7)
        resp_size, resp_type, resp_tag = struct.unpack("<IBH", resp_header)

        if resp_tag != tag:
            raise RuntimeError(f"Tag mismatch: expected {tag}, got {resp_tag}")

        payload_size = resp_size - 7
        resp_payload = self._recv_exact(payload_size) if payload_size > 0 else b""

        # Check for error
        if resp_type == Rerror:
            err_len = struct.unpack("<H", resp_payload[:2])[0]
            err_msg = resp_payload[2:2+err_len].decode("utf-8")
            raise RuntimeError(f"9P error: {err_msg}")

        return resp_type, resp_payload

    def _recv_exact(self, n: int) -> bytes:
        """Receive exactly n bytes."""
        data = b""
        while len(data) < n:
            chunk = self.sock.recv(n - len(data))
            if not chunk:
                raise RuntimeError("Connection closed")
            data += chunk
        return data

    def _version(self):
        """Perform version handshake."""
        version_str = b"9P2000"
        payload = struct.pack("<I", self.msize) + struct.pack("<H", len(version_str)) + version_str

        resp_type, resp_payload = self._send_recv(Tversion, payload)
        if resp_type != Rversion:
            raise RuntimeError(f"Version handshake failed: type {resp_type}")

        resp_msize = struct.unpack("<I", resp_payload[:4])[0]
        self.msize = min(self.msize, resp_msize)
        logger.debug(f"9P version negotiated, msize={self.msize}")

    def _attach(self):
        """Attach to the root of the filesystem."""
        self.root_fid = self._next_fid()
        afid = NOFID  # No auth

        uname = b"agent"
        aname = b""

        payload = (
            struct.pack("<I", self.root_fid) +
            struct.pack("<I", afid) +
            struct.pack("<H", len(uname)) + uname +
            struct.pack("<H", len(aname)) + aname
        )

        resp_type, resp_payload = self._send_recv(Tattach, payload)
        if resp_type != Rattach:
            raise RuntimeError(f"Attach failed: type {resp_type}")

        logger.debug(f"Attached to root, fid={self.root_fid}")

    def _walk(self, fid: int, newfid: int, path: str) -> Optional[bytes]:
        """Walk from fid to path, returning QID or None if not found."""
        # Parse path into components
        path = path.strip("/")
        if not path:
            wnames = []
        else:
            wnames = path.split("/")

        # Build walk message
        payload = struct.pack("<II", fid, newfid)
        payload += struct.pack("<H", len(wnames))
        for name in wnames:
            name_bytes = name.encode("utf-8")
            payload += struct.pack("<H", len(name_bytes)) + name_bytes

        try:
            resp_type, resp_payload = self._send_recv(Twalk, payload)
            if resp_type != Rwalk:
                return None

            # Parse nwqid
            nwqid = struct.unpack("<H", resp_payload[:2])[0]
            if nwqid != len(wnames) and len(wnames) > 0:
                return None

            # Return last QID
            if nwqid > 0:
                qid_offset = 2 + (nwqid - 1) * 13
                return resp_payload[qid_offset:qid_offset+13]
            return resp_payload[2:15] if len(resp_payload) >= 15 else b"\x00" * 13

        except RuntimeError as e:
            if "no such file" in str(e).lower() or "not found" in str(e).lower():
                return None
            raise

    def _open(self, fid: int, mode: int) -> bool:
        """Open a file."""
        payload = struct.pack("<IB", fid, mode)

        try:
            resp_type, resp_payload = self._send_recv(Topen, payload)
            return resp_type == Ropen
        except RuntimeError:
            return False

    def _read_all(self, fid: int) -> bytes:
        """Read all data from an open file."""
        data = b""
        offset = 0
        chunk_size = min(8192, self.msize - 100)

        while True:
            payload = struct.pack("<IQI", fid, offset, chunk_size)
            resp_type, resp_payload = self._send_recv(Tread, payload)

            if resp_type != Rread:
                break

            count = struct.unpack("<I", resp_payload[:4])[0]
            if count == 0:
                break

            data += resp_payload[4:4+count]
            offset += count

        return data

    def _write(self, fid: int, data: bytes) -> int:
        """Write data to an open file."""
        offset = 0
        total_written = 0
        chunk_size = min(8192, self.msize - 100)

        while offset < len(data):
            chunk = data[offset:offset+chunk_size]
            payload = struct.pack("<IQI", fid, offset, len(chunk)) + chunk

            resp_type, resp_payload = self._send_recv(Twrite, payload)

            if resp_type != Rwrite:
                break

            count = struct.unpack("<I", resp_payload[:4])[0]
            total_written += count
            offset += count

        return total_written

    def _clunk(self, fid: int):
        """Release a fid."""
        payload = struct.pack("<I", fid)
        try:
            self._send_recv(Tclunk, payload)
        except RuntimeError:
            pass  # Ignore clunk errors
