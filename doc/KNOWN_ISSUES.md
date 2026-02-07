# Known Issues & Limitations

This document tracks known issues that have not yet been fixed, along with their severity, impact, and potential workarounds.

---

## Medium Priority

### 1. SharedArrayBuffer Requires COOP/COEP Headers

**File**: `runtime/events.js`

**Status**: NOT FIXED (requires server configuration)

**Problem**: `SharedArrayBuffer` requires Cross-Origin-Opener-Policy and Cross-Origin-Embedder-Policy HTTP headers. Without them, `allocShared` fails with console error (not silently).

**Impact**: `SharedBuffer` features (shared memory between workers) don't work on most hosting environments.

**Workaround**: Configure your server to send these headers:
```
Cross-Origin-Opener-Policy: same-origin
Cross-Origin-Embedder-Policy: require-corp
```

Or use regular `ArrayBuffer` with message passing instead.

---

### 2. getScreenCTM() May Be Deprecated

**Files**:
- `runtime/reactive.js` line 641
- `runtime/svg-events.js` lines 17, 32

**Status**: NOT FIXED (browser support still good)

**Problem**: `SVGSVGElement.getScreenCTM()` is marked as deprecated in some documentation, though still widely supported.

**Impact**: May break in future browser versions.

**Workaround**: None needed currently. When browsers remove support, we'll need to implement manual matrix calculation using `getBoundingClientRect()` and SVG transform parsing.

**Tracking**: Monitor browser deprecation warnings in console.

---

### 3. Deep Equality Depth Limit

**File**: `runtime/reactive.js` lines 154-180

**Status**: NOT FIXED (edge case)

**Problem**: The `deepEqual` function has a hardcoded depth limit of 20 levels. Models with deeper nesting will fall back to reference equality, potentially missing updates.

**Impact**: Bindings on deeply nested fields (>20 levels) may not update correctly.

**Workaround**:
- Flatten deeply nested models
- Use explicit binding updates via message dispatch

---

### 4. JSON.parse Without Schema Validation

**Files**:
- `runtime/reactive.js` line 1107 (Big Lens)
- `runtime/primitives.js` line 299 (localStorage)

**Status**: NOT FIXED (low risk with Agda types)

**Problem**: JSON parsing doesn't validate that the parsed structure matches expected types. Malformed data could break type invariants.

**Impact**:
- Big Lens: Malformed "over:" messages become string messages
- localStorage: Invalid JSON returns `null`, indistinguishable from missing key

**Workaround**: Agda's type system prevents most issues at compile time. For external data, add validation in message handlers.

---

## Low Priority

### 5. O(n²) Slot Detection

**File**: `runtime/reactive.js` lines 217-231

**Status**: NOT FIXED (acceptable for most use cases)

**Problem**: `detectSlots` calls the extract function N+1 times for N slots. With large records (20+ fields), this becomes slow.

**Impact**: Performance degradation on models with many fields.

**Workaround**: Keep model records reasonably sized (<20 fields). Use nested records for larger data.

---

### 6. structuredClone Polyfill Limitations

**File**: `runtime/reactive.js` line 1142

**Status**: NOT FIXED (edge case)

**Problem**: When `structuredClone` is unavailable, falls back to `JSON.parse(JSON.stringify())` which loses class references, functions, and circular references.

**Impact**: Time-travel with complex model structures may lose data.

**Workaround**: Use modern browsers that support `structuredClone` (Chrome 98+, Firefox 94+, Safari 15.4+).

---

## API Design Notes

### Coordinate System Ambiguity

**Files**: `runtime/reactive.js` onValue vs onValueScreen

**Note**: `onValue` attempts SVG coordinate conversion and falls back to screen coords silently. `onValueScreen` always uses screen coords. Handlers can't distinguish which system was used.

**Recommendation**: See `src/Agdelte/Svg/Events.agda` header comment for when to use each:
- SVG coords: drawing, placing elements within SVG
- Screen coords: drag operations, UI gestures

---

## Contributing

When fixing any of these issues, please:
1. Remove the corresponding entry from this file
2. Add tests if applicable
3. Update the CHANGELOG

Last updated: 2026-02-07
