"""
Namespace Agent for AgentDojo evaluation.

This package provides a 9P-based agent that implements AgentDojo's
BasePipelineElement interface, enabling evaluation of namespace-bounded
security against the standard benchmark.
"""

from .agent import Namespace9PAgent
from .namespace import NamespaceSpec, MinimalNamespace, FullNamespace
from .runtime import P9Runtime
from .evaluator import NamespaceEvaluator

__version__ = "0.1.0"
__all__ = [
    "Namespace9PAgent",
    "NamespaceSpec",
    "MinimalNamespace",
    "FullNamespace",
    "P9Runtime",
    "NamespaceEvaluator",
]
