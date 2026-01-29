// Command server runs the combined AgentDojo 9P server.
//
// Usage:
//
//	server -addr :5640 -debug
package main

import (
	"flag"
	"log"

	"github.com/NERVsystems/nerva-9p-paper/experiments/agentdojo-integration/servers"
)

var (
	addr  = flag.String("addr", ":5640", "Address to listen on")
	debug = flag.Bool("debug", false, "Enable debug logging")
)

func main() {
	flag.Parse()

	cfg := &servers.ServerConfig{
		Address: *addr,
		Debug:   *debug,
	}

	log.Printf("Starting AgentDojo 9P server...")
	if err := servers.RunCombinedServer(cfg); err != nil {
		log.Fatalf("Server error: %v", err)
	}
}
