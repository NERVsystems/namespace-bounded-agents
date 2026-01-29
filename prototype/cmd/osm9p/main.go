// osm9p is a 9P server that exposes OpenStreetMap functionality as a filesystem.
//
// This is the prototype implementation for the AgentFS spec.
// It demonstrates how LLM agents can interact with services through filesystem
// semantics rather than traditional tool-calling protocols.
//
// Usage:
//
//	osm9p -addr :5640
//	# From Inferno:
//	mount -A tcp!localhost!5640 /n/osm
//	echo "Eiffel Tower, Paris" > /n/osm/geocode/query
//	cat /n/osm/geocode/query
package main

import (
	"bytes"
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log"
	"math"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/signal"
	"strconv"
	"strings"
	"syscall"
	"time"

	"github.com/NERVsystems/nerva-9p-paper/prototype/pkg/cassette"
	"github.com/NERVsystems/nerva-9p-paper/prototype/pkg/nerv9p"
)

var (
	version    = "0.2.0"
	addr       = flag.String("addr", ":5640", "Address to listen on")
	debug      = flag.Bool("debug", false, "Enable debug logging")
	recordFile = flag.String("record", "", "Record HTTP responses to cassette file")
	replayFile = flag.String("replay", "", "Replay HTTP responses from cassette file")
)

func main() {
	flag.Parse()

	log.Printf("osm9p server version %s (AgentFS spec v0)", version)

	// Determine cassette mode
	var mode cassette.Mode
	var cassettePath string
	if *recordFile != "" && *replayFile != "" {
		log.Fatal("Cannot specify both -record and -replay")
	} else if *recordFile != "" {
		mode = cassette.ModeRecord
		cassettePath = *recordFile
		log.Printf("Recording HTTP responses to: %s", cassettePath)
	} else if *replayFile != "" {
		mode = cassette.ModeReplay
		cassettePath = *replayFile
		log.Printf("Replaying HTTP responses from: %s", cassettePath)
	}

	// Create HTTP client with cassette recorder
	httpClient := &http.Client{Timeout: 30 * time.Second}
	recorder := cassette.NewRecorder(httpClient, mode, cassettePath)

	// Create root filesystem with tools
	root := createOSMService(recorder)

	// Create server
	srv := nerv9p.NewServer(root)
	srv.SetDebug(*debug)

	// Start listening
	listener, err := net.Listen("tcp", *addr)
	if err != nil {
		log.Fatalf("Failed to listen: %v", err)
	}
	defer listener.Close()

	log.Printf("Listening on %s", *addr)
	log.Printf("Mount with: mount -A tcp!localhost!%s /n/osm", (*addr)[1:])

	// Handle shutdown
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	go func() {
		sigCh := make(chan os.Signal, 1)
		signal.Notify(sigCh, syscall.SIGINT, syscall.SIGTERM)
		<-sigCh
		log.Println("Shutting down...")

		// Save cassette if recording
		if mode == cassette.ModeRecord {
			stats := recorder.GetStats()
			log.Printf("Saving cassette with %d recorded interactions", stats.Hits+stats.AliasHits+stats.Misses)
			if err := recorder.Save(); err != nil {
				log.Printf("Error saving cassette: %v", err)
			}
		}

		cancel()
		listener.Close()
	}()

	// Serve
	if err := srv.Serve(ctx, listener); err != nil && err != context.Canceled {
		log.Printf("Server error: %v", err)
	}

	// Final cassette stats and save
	if mode == cassette.ModeRecord {
		stats := recorder.GetStats()
		log.Printf("Final save: cassette with %d interactions", stats.Hits+stats.AliasHits+stats.Misses)
		if err := recorder.Save(); err != nil {
			log.Printf("Error saving cassette: %v", err)
		}
	} else if mode == cassette.ModeReplay {
		recorder.PrintStats()
	}
}

// HTTPClient is an interface for making HTTP requests (implemented by both http.Client and cassette.Recorder).
type HTTPClient interface {
	Do(req *http.Request) (*http.Response, error)
	Get(url string) (*http.Response, error)
	Post(url, contentType string, body io.Reader) (*http.Response, error)
}

// createOSMService creates the OSM service using AgentFS patterns.
//
// Type A tools (single input): geocode, reverse
// Type B tools (multi-parameter): nearby, distance, route, meeting_point, etc.
func createOSMService(client HTTPClient) *nerv9p.RootDir {
	root := nerv9p.NewRootDir()

	// === Type A Tools (single input) ===

	// geocode: write address, read coordinates
	root.AddChild(nerv9p.NewTypeATool(nerv9p.TypeAConfig{
		Name:    "geocode",
		Handler: geocodeHandler(client),
		TTL:     -1, // Cache indefinitely (addresses don't change)
		Types:   "query:string",
		Example: "echo 'Eiffel Tower, Paris' > query && cat query",
	}))

	// reverse: write "lat,lon", read address
	root.AddChild(nerv9p.NewTypeATool(nerv9p.TypeAConfig{
		Name:    "reverse",
		Handler: reverseHandler(client),
		TTL:     -1,
		Types:   "query:lat_lon",
		Example: "echo '48.8584,2.2945' > query && cat query",
	}))

	// === Type B Tools (multi-parameter) ===

	// nearby: find POIs near a location
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "nearby",
		Params:   []string{"lat", "lon", "radius", "category"},
		Required: []string{"lat", "lon", "category"},
		Handler:  nearbyHandler(client),
		TTL:      60000, // 1 minute cache (POIs can change)
		Types:    "lat:float lon:float radius:int category:string",
		Example:  "echo 48.8584 > lat; echo 2.2945 > lon; echo restaurant > category; cat result",
	}))

	// distance: calculate distance between two points
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "distance",
		Params:   []string{"lat1", "lon1", "lat2", "lon2"},
		Required: []string{"lat1", "lon1", "lat2", "lon2"},
		Handler:  distanceHandler(),
		TTL:      -1, // Pure calculation, cache forever
		Types:    "lat1:float lon1:float lat2:float lon2:float",
	}))

	// route: get directions between two points
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "route",
		Params:   []string{"start_lat", "start_lon", "end_lat", "end_lon", "mode"},
		Required: []string{"start_lat", "start_lon", "end_lat", "end_lon"},
		Handler:  routeHandler(client),
		TTL:      300000, // 5 minutes (routes can change with traffic)
		Types:    "start_lat:float start_lon:float end_lat:float end_lon:float mode:string",
	}))

	// centroid: calculate center point of multiple locations
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "centroid",
		Params:   []string{"points"},
		Required: []string{"points"},
		Handler:  centroidHandler(),
		TTL:      -1,
		Types:    "points:lat_lon_list",
		Example:  "echo -e '48.8584,2.2945\\n48.8606,2.3376' > points; cat result",
	}))

	// meeting_point: find a venue between locations
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "meeting_point",
		Params:   []string{"lat1", "lon1", "lat2", "lon2", "category"},
		Required: []string{"lat1", "lon1", "lat2", "lon2"},
		Handler:  meetingPointHandler(client),
		TTL:      60000,
		Types:    "lat1:float lon1:float lat2:float lon2:float category:string",
	}))

	// parking: find parking near a location
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "parking",
		Params:   []string{"lat", "lon", "radius"},
		Required: []string{"lat", "lon"},
		Handler:  parkingHandler(client),
		TTL:      60000,
		Types:    "lat:float lon:float radius:int",
	}))

	// charging: find EV charging stations
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "charging",
		Params:   []string{"lat", "lon", "radius"},
		Required: []string{"lat", "lon"},
		Handler:  chargingHandler(client),
		TTL:      60000,
		Types:    "lat:float lon:float radius:int",
	}))

	// schools: find schools near a location
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "schools",
		Params:   []string{"lat", "lon", "radius"},
		Required: []string{"lat", "lon"},
		Handler:  schoolsHandler(client),
		TTL:      86400000, // 24 hours (schools don't move)
		Types:    "lat:float lon:float radius:int",
	}))

	// explore: discover what's in an area
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "explore",
		Params:   []string{"lat", "lon", "radius"},
		Required: []string{"lat", "lon"},
		Handler:  exploreHandler(client),
		TTL:      60000,
		Types:    "lat:float lon:float radius:int",
	}))

	// bbox: create bounding box from points
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "bbox",
		Params:   []string{"points"},
		Required: []string{"points"},
		Handler:  bboxHandler(),
		TTL:      -1,
		Types:    "points:lat_lon_list",
	}))

	// polyline_decode: decode Google polyline format
	root.AddChild(nerv9p.NewTypeATool(nerv9p.TypeAConfig{
		Name:    "polyline_decode",
		Handler: polylineDecodeHandler(),
		TTL:     -1,
		Types:   "query:string",
	}))

	// polyline_encode: encode points to polyline format
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "polyline_encode",
		Params:   []string{"points"},
		Required: []string{"points"},
		Handler:  polylineEncodeHandler(),
		TTL:      -1,
		Types:    "points:lat_lon_list",
	}))

	return root
}

// =============================================================================
// Type A Handlers (single input -> output)
// =============================================================================

func geocodeHandler(client HTTPClient) nerv9p.TypeAHandler {
	return func(input []byte) ([]byte, error) {
		address := string(bytes.TrimSpace(input))
		if address == "" {
			return nil, nerv9p.NewAgentError("missing_input", "address required", false)
		}

		params := url.Values{}
		params.Set("q", address)
		params.Set("format", "json")
		params.Set("limit", "1")

		req, _ := http.NewRequest("GET", "https://nominatim.openstreetmap.org/search?"+params.Encode(), nil)
		req.Header.Set("User-Agent", "osm9p/0.2.0 (AgentFS research prototype)")

		resp, err := client.Do(req)
		if err != nil {
			return nil, nerv9p.NewAgentError("api_error", fmt.Sprintf("geocoding failed: %v", err), true)
		}
		defer resp.Body.Close()

		var results []struct {
			Lat         string `json:"lat"`
			Lon         string `json:"lon"`
			DisplayName string `json:"display_name"`
		}
		if err := json.NewDecoder(resp.Body).Decode(&results); err != nil {
			return nil, nerv9p.NewAgentError("parse_error", fmt.Sprintf("failed to parse response: %v", err), true)
		}

		if len(results) == 0 {
			return nerv9p.JSONResult(map[string]interface{}{
				"error": "not_found",
				"query": address,
			}), nil
		}

		return nerv9p.JSONResult(map[string]interface{}{
			"lat":          results[0].Lat,
			"lon":          results[0].Lon,
			"display_name": results[0].DisplayName,
		}), nil
	}
}

func reverseHandler(client HTTPClient) nerv9p.TypeAHandler {
	return func(input []byte) ([]byte, error) {
		parts := strings.Split(string(bytes.TrimSpace(input)), ",")
		if len(parts) != 2 {
			return nil, nerv9p.NewAgentError("invalid_input", "expected lat,lon format", false)
		}

		lat, err1 := strconv.ParseFloat(strings.TrimSpace(parts[0]), 64)
		lon, err2 := strconv.ParseFloat(strings.TrimSpace(parts[1]), 64)
		if err1 != nil || err2 != nil {
			return nil, nerv9p.NewAgentError("invalid_input", "invalid coordinates", false)
		}

		params := url.Values{}
		params.Set("lat", fmt.Sprintf("%f", lat))
		params.Set("lon", fmt.Sprintf("%f", lon))
		params.Set("format", "json")

		req, _ := http.NewRequest("GET", "https://nominatim.openstreetmap.org/reverse?"+params.Encode(), nil)
		req.Header.Set("User-Agent", "osm9p/0.2.0 (AgentFS research prototype)")

		resp, err := client.Do(req)
		if err != nil {
			return nil, nerv9p.NewAgentError("api_error", fmt.Sprintf("reverse geocoding failed: %v", err), true)
		}
		defer resp.Body.Close()

		var result map[string]interface{}
		if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
			return nil, nerv9p.NewAgentError("parse_error", fmt.Sprintf("failed to parse response: %v", err), true)
		}

		return nerv9p.JSONResult(result), nil
	}
}

func polylineDecodeHandler() nerv9p.TypeAHandler {
	return func(input []byte) ([]byte, error) {
		polyline := string(bytes.TrimSpace(input))
		if polyline == "" {
			return nil, nerv9p.NewAgentError("missing_input", "polyline string required", false)
		}

		points := decodePolyline(polyline)
		return nerv9p.JSONResult(map[string]interface{}{
			"points": points,
			"count":  len(points),
		}), nil
	}
}

// =============================================================================
// Type B Handlers (multi-parameter -> output)
// =============================================================================

func nearbyHandler(client HTTPClient) nerv9p.TypeBHandler {
	return func(params map[string]string) ([]byte, error) {
		lat, _ := strconv.ParseFloat(params["lat"], 64)
		lon, _ := strconv.ParseFloat(params["lon"], 64)
		radius, _ := strconv.ParseFloat(params["radius"], 64)
		category := params["category"]

		if radius == 0 {
			radius = 1000
		}

		query := fmt.Sprintf(`
			[out:json][timeout:25];
			(
				node["amenity"="%s"](around:%f,%f,%f);
				way["amenity"="%s"](around:%f,%f,%f);
			);
			out center 10;
		`, category, radius, lat, lon, category, radius, lat, lon)

		result, err := overpassQuery(client, query)
		if err != nil {
			return nil, err
		}
		return nerv9p.JSONResult(result), nil
	}
}

func distanceHandler() nerv9p.TypeBHandler {
	return func(params map[string]string) ([]byte, error) {
		lat1, _ := strconv.ParseFloat(params["lat1"], 64)
		lon1, _ := strconv.ParseFloat(params["lon1"], 64)
		lat2, _ := strconv.ParseFloat(params["lat2"], 64)
		lon2, _ := strconv.ParseFloat(params["lon2"], 64)

		distance := haversine(lat1, lon1, lat2, lon2)
		return nerv9p.JSONResult(map[string]interface{}{
			"distance_meters": distance,
			"distance_km":     distance / 1000,
		}), nil
	}
}

func routeHandler(client HTTPClient) nerv9p.TypeBHandler {
	return func(params map[string]string) ([]byte, error) {
		startLat, _ := strconv.ParseFloat(params["start_lat"], 64)
		startLon, _ := strconv.ParseFloat(params["start_lon"], 64)
		endLat, _ := strconv.ParseFloat(params["end_lat"], 64)
		endLon, _ := strconv.ParseFloat(params["end_lon"], 64)
		mode := params["mode"]

		profile := "car"
		switch mode {
		case "foot", "walking":
			profile = "foot"
		case "bike", "cycling":
			profile = "bike"
		}

		reqURL := fmt.Sprintf(
			"https://router.project-osrm.org/route/v1/%s/%f,%f;%f,%f?overview=full&geometries=geojson",
			profile, startLon, startLat, endLon, endLat,
		)

		resp, err := client.Get(reqURL)
		if err != nil {
			return nil, nerv9p.NewAgentError("api_error", fmt.Sprintf("routing failed: %v", err), true)
		}
		defer resp.Body.Close()

		var result map[string]interface{}
		if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
			return nil, nerv9p.NewAgentError("parse_error", fmt.Sprintf("failed to parse response: %v", err), true)
		}
		return nerv9p.JSONResult(result), nil
	}
}

func centroidHandler() nerv9p.TypeBHandler {
	return func(params map[string]string) ([]byte, error) {
		pointsStr := params["points"]

		// Bounds check
		if len(pointsStr) > nerv9p.MaxParamBytes {
			return nil, nerv9p.NewInputTooLargeError("points", nerv9p.MaxParamBytes, len(pointsStr))
		}

		// Accept both newline and semicolon as delimiters
		pointsStr = strings.ReplaceAll(pointsStr, ";", "\n")
		lines := strings.Split(pointsStr, "\n")

		var sumLat, sumLon float64
		var canonical []string
		count := 0
		for _, line := range lines {
			line = strings.TrimSpace(line)
			if line == "" {
				continue
			}
			if count >= nerv9p.MaxPointsCount {
				return nil, nerv9p.NewInputTooLargeError("points", nerv9p.MaxPointsCount, len(lines))
			}
			parts := strings.Split(line, ",")
			if len(parts) != 2 {
				continue
			}
			lat, _ := strconv.ParseFloat(strings.TrimSpace(parts[0]), 64)
			lon, _ := strconv.ParseFloat(strings.TrimSpace(parts[1]), 64)
			sumLat += lat
			sumLon += lon
			canonical = append(canonical, fmt.Sprintf("%f,%f", lat, lon))
			count++
		}

		if count == 0 {
			return nil, nerv9p.NewFormatError("points", "expected lat,lon pairs separated by newlines or semicolons", []string{"points"})
		}

		return nerv9p.JSONResult(map[string]interface{}{
			"lat":       sumLat / float64(count),
			"lon":       sumLon / float64(count),
			"_parsed":   count,
			"_canonical": strings.Join(canonical, "\n"),
		}), nil
	}
}

func meetingPointHandler(client HTTPClient) nerv9p.TypeBHandler {
	return func(params map[string]string) ([]byte, error) {
		lat1, _ := strconv.ParseFloat(params["lat1"], 64)
		lon1, _ := strconv.ParseFloat(params["lon1"], 64)
		lat2, _ := strconv.ParseFloat(params["lat2"], 64)
		lon2, _ := strconv.ParseFloat(params["lon2"], 64)
		category := params["category"]

		if category == "" {
			category = "cafe"
		}

		centerLat := (lat1 + lat2) / 2
		centerLon := (lon1 + lon2) / 2

		query := fmt.Sprintf(`
			[out:json][timeout:25];
			(
				node["amenity"="%s"](around:1000,%f,%f);
			);
			out center 5;
		`, category, centerLat, centerLon)

		venues, err := overpassQuery(client, query)
		if err != nil {
			return nil, err
		}

		return nerv9p.JSONResult(map[string]interface{}{
			"centroid": map[string]interface{}{
				"lat": centerLat,
				"lon": centerLon,
			},
			"venues": venues,
		}), nil
	}
}

func parkingHandler(client HTTPClient) nerv9p.TypeBHandler {
	return categorySearchHandler(client, "parking", 1000)
}

func chargingHandler(client HTTPClient) nerv9p.TypeBHandler {
	return func(params map[string]string) ([]byte, error) {
		lat, _ := strconv.ParseFloat(params["lat"], 64)
		lon, _ := strconv.ParseFloat(params["lon"], 64)
		radius, _ := strconv.ParseFloat(params["radius"], 64)
		if radius == 0 {
			radius = 1000
		}

		query := fmt.Sprintf(`
			[out:json][timeout:25];
			(
				node["amenity"="charging_station"](around:%f,%f,%f);
				way["amenity"="charging_station"](around:%f,%f,%f);
			);
			out center 10;
		`, radius, lat, lon, radius, lat, lon)

		result, err := overpassQuery(client, query)
		if err != nil {
			return nil, err
		}
		return nerv9p.JSONResult(result), nil
	}
}

func schoolsHandler(client HTTPClient) nerv9p.TypeBHandler {
	return func(params map[string]string) ([]byte, error) {
		lat, _ := strconv.ParseFloat(params["lat"], 64)
		lon, _ := strconv.ParseFloat(params["lon"], 64)
		radius, _ := strconv.ParseFloat(params["radius"], 64)
		if radius == 0 {
			radius = 2000
		}

		query := fmt.Sprintf(`
			[out:json][timeout:25];
			(
				node["amenity"="school"](around:%f,%f,%f);
				way["amenity"="school"](around:%f,%f,%f);
				node["amenity"="kindergarten"](around:%f,%f,%f);
				way["amenity"="kindergarten"](around:%f,%f,%f);
			);
			out center 10;
		`, radius, lat, lon, radius, lat, lon, radius, lat, lon, radius, lat, lon)

		result, err := overpassQuery(client, query)
		if err != nil {
			return nil, err
		}
		return nerv9p.JSONResult(result), nil
	}
}

func exploreHandler(client HTTPClient) nerv9p.TypeBHandler {
	return func(params map[string]string) ([]byte, error) {
		lat, _ := strconv.ParseFloat(params["lat"], 64)
		lon, _ := strconv.ParseFloat(params["lon"], 64)
		radius, _ := strconv.ParseFloat(params["radius"], 64)
		if radius == 0 {
			radius = 500
		}

		query := fmt.Sprintf(`
			[out:json][timeout:25];
			(
				node["amenity"](around:%f,%f,%f);
				node["shop"](around:%f,%f,%f);
				node["tourism"](around:%f,%f,%f);
			);
			out center 20;
		`, radius, lat, lon, radius, lat, lon, radius, lat, lon)

		result, err := overpassQuery(client, query)
		if err != nil {
			return nil, err
		}
		return nerv9p.JSONResult(result), nil
	}
}

func bboxHandler() nerv9p.TypeBHandler {
	return func(params map[string]string) ([]byte, error) {
		pointsStr := params["points"]

		// Bounds check
		if len(pointsStr) > nerv9p.MaxParamBytes {
			return nil, nerv9p.NewInputTooLargeError("points", nerv9p.MaxParamBytes, len(pointsStr))
		}

		// Accept both newline and semicolon as delimiters, also space-separated points
		pointsStr = strings.ReplaceAll(pointsStr, ";", "\n")
		pointsStr = strings.ReplaceAll(pointsStr, " ", "\n")
		lines := strings.Split(pointsStr, "\n")

		minLat, maxLat := 90.0, -90.0
		minLon, maxLon := 180.0, -180.0
		var canonical []string
		count := 0

		for _, line := range lines {
			line = strings.TrimSpace(line)
			if line == "" {
				continue
			}
			if count >= nerv9p.MaxPointsCount {
				return nil, nerv9p.NewInputTooLargeError("points", nerv9p.MaxPointsCount, len(lines))
			}
			parts := strings.Split(line, ",")
			if len(parts) != 2 {
				continue
			}
			lat, _ := strconv.ParseFloat(strings.TrimSpace(parts[0]), 64)
			lon, _ := strconv.ParseFloat(strings.TrimSpace(parts[1]), 64)

			if lat < minLat {
				minLat = lat
			}
			if lat > maxLat {
				maxLat = lat
			}
			if lon < minLon {
				minLon = lon
			}
			if lon > maxLon {
				maxLon = lon
			}
			canonical = append(canonical, fmt.Sprintf("%f,%f", lat, lon))
			count++
		}

		if count == 0 {
			return nil, nerv9p.NewFormatError("points", "expected lat,lon pairs separated by newlines, semicolons, or spaces", []string{"points"})
		}

		return nerv9p.JSONResult(map[string]interface{}{
			"min_lat":    minLat,
			"min_lon":    minLon,
			"max_lat":    maxLat,
			"max_lon":    maxLon,
			"_parsed":    count,
			"_canonical": strings.Join(canonical, "\n"),
		}), nil
	}
}

func polylineEncodeHandler() nerv9p.TypeBHandler {
	return func(params map[string]string) ([]byte, error) {
		pointsStr := params["points"]

		// Bounds check
		if len(pointsStr) > nerv9p.MaxParamBytes {
			return nil, nerv9p.NewInputTooLargeError("points", nerv9p.MaxParamBytes, len(pointsStr))
		}

		// Accept both newline and semicolon as delimiters
		pointsStr = strings.ReplaceAll(pointsStr, ";", "\n")
		lines := strings.Split(pointsStr, "\n")

		var coords [][]float64
		var canonical []string
		for _, line := range lines {
			line = strings.TrimSpace(line)
			if line == "" {
				continue
			}
			if len(coords) >= nerv9p.MaxPointsCount {
				return nil, nerv9p.NewInputTooLargeError("points", nerv9p.MaxPointsCount, len(lines))
			}
			parts := strings.Split(line, ",")
			if len(parts) != 2 {
				continue
			}
			lat, _ := strconv.ParseFloat(strings.TrimSpace(parts[0]), 64)
			lon, _ := strconv.ParseFloat(strings.TrimSpace(parts[1]), 64)
			coords = append(coords, []float64{lat, lon})
			canonical = append(canonical, fmt.Sprintf("%f,%f", lat, lon))
		}

		if len(coords) == 0 {
			return nil, nerv9p.NewFormatError("points", "expected lat,lon pairs separated by newlines or semicolons", []string{"points"})
		}

		polyline := encodePolyline(coords)
		return nerv9p.JSONResult(map[string]interface{}{
			"polyline":   polyline,
			"_parsed":    len(coords),
			"_canonical": strings.Join(canonical, "\n"),
		}), nil
	}
}

// =============================================================================
// Helper Functions
// =============================================================================

func categorySearchHandler(client HTTPClient, category string, defaultRadius float64) nerv9p.TypeBHandler {
	return func(params map[string]string) ([]byte, error) {
		lat, _ := strconv.ParseFloat(params["lat"], 64)
		lon, _ := strconv.ParseFloat(params["lon"], 64)
		radius, _ := strconv.ParseFloat(params["radius"], 64)
		if radius == 0 {
			radius = defaultRadius
		}

		query := fmt.Sprintf(`
			[out:json][timeout:25];
			(
				node["amenity"="%s"](around:%f,%f,%f);
				way["amenity"="%s"](around:%f,%f,%f);
			);
			out center 10;
		`, category, radius, lat, lon, category, radius, lat, lon)

		result, err := overpassQuery(client, query)
		if err != nil {
			return nil, err
		}
		return nerv9p.JSONResult(result), nil
	}
}

func overpassQuery(client HTTPClient, query string) (interface{}, error) {
	resp, err := client.Post(
		"https://overpass-api.de/api/interpreter",
		"application/x-www-form-urlencoded",
		bytes.NewBufferString("data="+url.QueryEscape(query)),
	)
	if err != nil {
		return nil, nerv9p.NewAgentError("api_error", fmt.Sprintf("overpass query failed: %v", err), true)
	}
	defer resp.Body.Close()

	var result map[string]interface{}
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		return nil, nerv9p.NewAgentError("parse_error", fmt.Sprintf("failed to parse response: %v", err), true)
	}
	return result, nil
}

func haversine(lat1, lon1, lat2, lon2 float64) float64 {
	const R = 6371000 // Earth radius in meters

	φ1 := lat1 * math.Pi / 180
	φ2 := lat2 * math.Pi / 180
	Δφ := (lat2 - lat1) * math.Pi / 180
	Δλ := (lon2 - lon1) * math.Pi / 180

	a := math.Sin(Δφ/2)*math.Sin(Δφ/2) +
		math.Cos(φ1)*math.Cos(φ2)*
			math.Sin(Δλ/2)*math.Sin(Δλ/2)
	c := 2 * math.Atan2(math.Sqrt(a), math.Sqrt(1-a))

	return R * c
}

// Polyline encoding/decoding (Google format)

func decodePolyline(encoded string) []map[string]interface{} {
	var points []map[string]interface{}
	index, lat, lon := 0, 0, 0

	for index < len(encoded) {
		// Decode latitude
		shift, result := 0, 0
		for {
			b := int(encoded[index]) - 63
			index++
			result |= (b & 0x1f) << shift
			shift += 5
			if b < 0x20 {
				break
			}
		}
		if result&1 != 0 {
			lat += ^(result >> 1)
		} else {
			lat += result >> 1
		}

		// Decode longitude
		shift, result = 0, 0
		for {
			b := int(encoded[index]) - 63
			index++
			result |= (b & 0x1f) << shift
			shift += 5
			if b < 0x20 {
				break
			}
		}
		if result&1 != 0 {
			lon += ^(result >> 1)
		} else {
			lon += result >> 1
		}

		points = append(points, map[string]interface{}{
			"lat": float64(lat) / 1e5,
			"lon": float64(lon) / 1e5,
		})
	}

	return points
}

func encodePolyline(coords [][]float64) string {
	var encoded strings.Builder
	prevLat, prevLon := 0, 0

	for _, coord := range coords {
		lat := int(coord[0] * 1e5)
		lon := int(coord[1] * 1e5)

		encodeDiff(&encoded, lat-prevLat)
		encodeDiff(&encoded, lon-prevLon)

		prevLat, prevLon = lat, lon
	}

	return encoded.String()
}

func encodeDiff(buf *strings.Builder, diff int) {
	if diff < 0 {
		diff = ^(diff << 1)
	} else {
		diff <<= 1
	}

	for diff >= 0x20 {
		buf.WriteByte(byte((diff & 0x1f) | 0x20 + 63))
		diff >>= 5
	}
	buf.WriteByte(byte(diff + 63))
}
