package nerv9p

import (
	"testing"
)

func TestCanonicalizeInput(t *testing.T) {
	tests := []struct {
		name   string
		raw    string
		params []string
		want   string
	}{
		{
			name:   "already kv",
			raw:    "lat=48.85 lon=2.29",
			params: []string{"lat", "lon"},
			want:   "lat=48.85 lon=2.29",
		},
		{
			name:   "positional to kv",
			raw:    "48.85 2.29",
			params: []string{"lat", "lon"},
			want:   "lat=48.85 lon=2.29",
		},
		{
			name:   "partial kv with extra params",
			raw:    "lat=48.85 lon=2.29 radius=500 category=restaurant",
			params: []string{"lat", "lon", "radius", "category"},
			want:   "lat=48.85 lon=2.29 radius=500 category=restaurant",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := CanonicalizeInput(tt.raw, tt.params)
			if got != tt.want {
				t.Errorf("CanonicalizeInput() = %q, want %q", got, tt.want)
			}
		})
	}
}

func TestMissingParamRewriter(t *testing.T) {
	rw := &MissingParamRewriter{}

	tests := []struct {
		name     string
		raw      string
		err      ErrorPayload
		params   []string
		wantKV   string
		wantTerm bool
	}{
		{
			name: "partial kv - already has values, nothing to fill",
			raw:  "lat=48.85 lon=2.29",
			err: ErrorPayload{
				Code:     "missing_param",
				Missing:  []string{"category"},
				Expected: []string{"lat", "lon", "radius", "category"},
			},
			params:   []string{"lat", "lon", "radius", "category"},
			wantTerm: true, // terminal because we can't fill 'category' from nothing
		},
		{
			name: "positional input",
			raw:  "48.85 2.29 500 restaurant",
			err: ErrorPayload{
				Code:     "missing_param",
				Missing:  []string{"lat", "lon", "radius", "category"},
				Expected: []string{"lat", "lon", "radius", "category"},
			},
			params: []string{"lat", "lon", "radius", "category"},
			wantKV: "lat=48.85 lon=2.29 radius=500 category=restaurant",
		},
		{
			name: "partial kv with positional values to fill",
			raw:  "lat=48.85 lon=2.29 restaurant",
			err: ErrorPayload{
				Code:     "missing_param",
				Missing:  []string{"category"},
				Expected: []string{"lat", "lon", "radius", "category"},
			},
			params: []string{"lat", "lon", "radius", "category"},
			wantKV: "lat=48.85 lon=2.29 category=restaurant",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result, err := rw.Rewrite(tt.raw, tt.err, tt.params, "")
			if err != nil {
				t.Fatalf("Rewrite() error = %v", err)
			}
			if tt.wantTerm && !result.Terminal {
				t.Error("expected terminal")
			}
			if !tt.wantTerm && result.RewrittenInput != tt.wantKV {
				t.Errorf("Rewrite() = %q, want %q", result.RewrittenInput, tt.wantKV)
			}
		})
	}
}

func TestUnknownParamRewriter(t *testing.T) {
	rw := &UnknownParamRewriter{}

	tests := []struct {
		name     string
		raw      string
		err      ErrorPayload
		params   []string
		wantKV   string
		wantTerm bool
	}{
		{
			name: "amenity to category",
			raw:  "lat=48.85 lon=2.29 amenity=restaurant",
			err: ErrorPayload{
				Code:     "unknown_param",
				Expected: []string{"lat", "lon", "radius", "category"},
			},
			params: []string{"lat", "lon", "radius", "category"},
			wantKV: "lat=48.85 lon=2.29 category=restaurant",
		},
		{
			name: "poi_type to category",
			raw:  "lat1=48.85 lon1=2.29 lat2=48.86 lon2=2.34 poi_type=cafe",
			err: ErrorPayload{
				Code:     "unknown_param",
				Expected: []string{"lat1", "lon1", "lat2", "lon2", "category"},
			},
			params: []string{"lat1", "lon1", "lat2", "lon2", "category"},
			wantKV: "lat1=48.85 lon1=2.29 lat2=48.86 lon2=2.34 category=cafe",
		},
		{
			name: "lng to lon",
			raw:  "lat=48.85 lng=2.29",
			err: ErrorPayload{
				Code:     "unknown_param",
				Expected: []string{"lat", "lon"},
			},
			params: []string{"lat", "lon"},
			wantKV: "lat=48.85 lon=2.29",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result, err := rw.Rewrite(tt.raw, tt.err, tt.params, "")
			if err != nil {
				t.Fatalf("Rewrite() error = %v", err)
			}
			if tt.wantTerm && !result.Terminal {
				t.Error("expected terminal")
			}
			if !tt.wantTerm && result.RewrittenInput != tt.wantKV {
				t.Errorf("Rewrite() = %q, want %q", result.RewrittenInput, tt.wantKV)
			}
		})
	}
}

func TestFormatErrorRewriter(t *testing.T) {
	rw := &FormatErrorRewriter{}

	tests := []struct {
		name     string
		raw      string
		err      ErrorPayload
		params   []string
		example  string
		wantKV   string
		wantTerm bool
	}{
		{
			name: "semicolon to newline points",
			raw:  "points=48.85,2.29;48.86,2.34",
			err: ErrorPayload{
				Code:     "format_error",
				Expected: []string{"points"},
			},
			params: []string{"points"},
			wantKV: "points=48.85,2.29\n48.86,2.34",
		},
		{
			name: "multiple space-separated points",
			raw:  "points=48.85,2.29 48.86,2.34",
			err: ErrorPayload{
				Code:     "format_error",
				Expected: []string{"points"},
			},
			params: []string{"points"},
			wantKV: "points=48.85,2.29\n48.86,2.34",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result, err := rw.Rewrite(tt.raw, tt.err, tt.params, tt.example)
			if err != nil {
				t.Fatalf("Rewrite() error = %v", err)
			}
			if tt.wantTerm && !result.Terminal {
				t.Error("expected terminal")
			}
			if !tt.wantTerm && result.RewrittenInput != tt.wantKV {
				t.Errorf("Rewrite() = %q, want %q", result.RewrittenInput, tt.wantKV)
			}
		})
	}
}

func TestLevenshtein(t *testing.T) {
	tests := []struct {
		a, b string
		want int
	}{
		{"", "", 0},
		{"a", "", 1},
		{"", "a", 1},
		{"abc", "abc", 0},
		{"abc", "ab", 1},
		{"abc", "abd", 1},
		{"amenity", "category", 5}, // different enough to not match
		{"categroy", "category", 2}, // typo, close
	}

	for _, tt := range tests {
		t.Run(tt.a+"-"+tt.b, func(t *testing.T) {
			got := levenshtein(tt.a, tt.b)
			if got != tt.want {
				t.Errorf("levenshtein(%q, %q) = %d, want %d", tt.a, tt.b, got, tt.want)
			}
		})
	}
}

func TestFuzzyMatch(t *testing.T) {
	candidates := []string{"lat", "lon", "radius", "category"}

	tests := []struct {
		input   string
		maxDist int
		want    string
	}{
		{"lat", 2, "lat"},              // exact (distance 0)
		{"lat1", 2, "lat"},             // close to lat (distance 1)
		{"categroy", 2, "category"},    // typo
		{"raduis", 2, "radius"},        // typo
		{"amenity", 2, ""},             // too different (distance 5)
	}

	for _, tt := range tests {
		t.Run(tt.input, func(t *testing.T) {
			got := fuzzyMatch(tt.input, candidates, tt.maxDist)
			if got != tt.want {
				t.Errorf("fuzzyMatch(%q) = %q, want %q", tt.input, got, tt.want)
			}
		})
	}
}
