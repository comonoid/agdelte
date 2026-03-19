# Video Player — Design

## Overview

Custom video player component built on `MediaSource API` (not `<video src="...">`),
to allow segmented delivery and future integration of content protection.

### Existing constructs used (already in the codebase — do not redefine)

| Construct | Module | What it is |
|---|---|---|
| `Node`, `Attr`, `Binding` | `Agdelte.Reactive.Node.Core` | Core reactive template types |
| `elem`, `text`, `bind`, `when`, `whenT`, `foreach`, `foreachKeyed`, `scope`, `zoomRT` | `Agdelte.Reactive.Node.Core` | Node constructors |
| `attr`, `attrBind`, `on`, `onValue`, `onValueFrom`, `style`, `styleBind`, `onKeyFiltered` | `Agdelte.Reactive.Node.Core` | Attr constructors |
| `mkBinding`, `stringBinding`, `boolBinding` | `Agdelte.Reactive.Node.Core` | Binding helpers |
| `mkTransition`, `Transition` | `Agdelte.Reactive.Node.Core` | Enter/leave CSS transitions |
| `div`, `span`, `button`, `input`, `video`, `audio`, `source` | `Agdelte.Reactive.Node.Html` | Element smart constructors |
| `class`, `id'`, `value`, `valueBind`, `type'`, `onClick`, `onInput`, `onMouseMove`, `onMouseEnter` | `Agdelte.Reactive.Node.Html` | Attribute/event helpers |
| `onTimeUpdate`, `onLoadedMetadata`, `onVolumeChange`, `onEnded` | `Agdelte.Reactive.Node.Html` | Media event helpers |
| `Cmd`, `ε`, `_<>_`, `callMethod`, `setProp`, `getProp`, `attempt`, `delay`, `httpGet` | `Agdelte.Core.Cmd` | Command constructors |
| `Task`, `_>>=_`, `pure`, `fail` | `Agdelte.Core.Task` | Monadic task composition |
| `Event`, `never`, `sub`, `merge`, `timeout` | `Agdelte.Core.Event` | Event subscription combinators |
| `mapE`, `filterE` | `Agdelte.Core.Event` | Event transformers |
| `ReactiveApp` | `Agdelte.Reactive.Node.Core` | TEA app record (init, update, template, cmd, subs) |
| `eqStr` | `Agdelte.Html.Controls.Util` | String equality as Bool |
| `zoomNode`, `focusBinding` | `Agdelte.Reactive.Node.Zoom` | Model/Msg composition |

## Module structure

```
src/Agdelte/Html/Controls/Video/
  Player.agda        — state machine, public API, top-level component
  Controls.agda      — UI overlay (play/pause, seek bar, volume, time, fullscreen)
  Source.agda         — MediaSource + SourceBuffer management
  SegmentLoader.agda  — segment fetching pipeline (URL → ArrayBuffer)
  Types.agda          — shared types: PlayerState, SegmentInfo, Manifest, configs
  Util.agda           — JS postulates for time formatting, clamping, etc.

src/Agdelte/Css/Controls/Video.agda  — BEM-style CSS rules for the player
```

After implementation, re-export from `src/Agdelte/Html/Controls.agda`:
```agda
open import Agdelte.Html.Controls.Video.Player public
  renaming ( play to videoPlay ; pause to videoPause ... )
```

## Architecture

### Core modules

- **Types** — shared types used across all Video modules. No dependencies on
  other Video modules. Imported by Player, Controls, Source, SegmentLoader.
- **Player** — top-level component: state machine (idle → loading → playing → paused → ended),
  public API (play, pause, seek, volume, fullscreen). Owns the `<video>` element.
- **Controls** — UI overlay: play/pause, seek bar, volume, time display, fullscreen toggle.
  Pure `Node VideoModel VideoMsg` — consumes player state via bindings, emits `VideoMsg`.
- **Source** — media loading via `MediaSource` + `SourceBuffer`. Fetches and appends
  video segments. Abstraction point for future encryption/protection layer.
- **SegmentLoader** — fetches individual segments by URL. Isolated from Source
  so that authentication (signed URLs), decryption (AES-128), and variant
  selection (A/B watermarking) can be injected as middleware without touching
  playback logic.

### Why MediaSource from the start

Direct `<video src>` exposes a downloadable URL and makes it hard to retrofit
segmented delivery or chunk-level encryption later. Starting with `MediaSource`
means protection features layer on naturally without rewriting playback logic.

## Types (Types.agda)

### PlayerState

```agda
data PlayerState : Set where
  Idle Loading Playing Paused Ended Error : PlayerState

-- Decidable equality (needed for `when` predicates in templates)
-- Pattern: same as eqStr in Controls.Util, but for PlayerState
isPlaying : PlayerState → Bool
isPlaying Playing = true
isPlaying _       = false

eqState : PlayerState → PlayerState → Bool
eqState Idle Idle = true
eqState Loading Loading = true
eqState Playing Playing = true
eqState Paused Paused = true
eqState Ended Ended = true
eqState Error Error = true
eqState _ _ = false
```

### VideoModel

Follows the record-config pattern used by SliderConfig, AccordionConfig, etc.

```agda
record VideoModel : Set where
  field
    state         : PlayerState
    currentTime   : String         -- seconds as String (from DOM target.currentTime)
    duration      : String         -- seconds as String (from DOM target.duration)
    volume        : String         -- [0..1] as String
    muted         : Bool
    fullscreen    : Bool
    buffered      : String         -- furthest buffered position, seconds as String
    playbackRate  : String         -- "1" default
    error          : Maybe String   -- last error message, if any
    controlsVisible : Bool          -- whether controls overlay is shown
    -- Segment tracking (for Source module)
    currentSegment : ℕ
    totalSegments  : ℕ
    segmentUrls    : String         -- JSON array of segment URLs (from parsed manifest)
    manifestUrl    : String
    sourceReady    : Bool           -- MediaSource is open and ready for appends
```

All numeric fields are `String` — consistent with existing controls (Slider uses
`String` for min/max/value since DOM APIs traffic in strings, and Agda's JS backend
has no native Float↔String round-trip). Parsing happens in JS postulates.

```agda
defaultVideoModel : VideoModel
defaultVideoModel = record
  { state = Idle ; currentTime = "0" ; duration = "0" ; volume = "0.8"
  ; muted = false ; fullscreen = false ; buffered = "0" ; playbackRate = "1"
  ; error = nothing ; controlsVisible = true
  ; currentSegment = 0 ; totalSegments = 0 ; segmentUrls = "[]"
  ; manifestUrl = "" ; sourceReady = false }
```

### VideoMsg

```agda
data VideoMsg : Set where
  -- Playback
  Play Pause TogglePlay : VideoMsg
  Seek        : String → VideoMsg       -- target time as String
  SetVolume   : String → VideoMsg       -- target volume as String
  ToggleMute  : VideoMsg
  SetRate     : String → VideoMsg       -- playback rate
  -- Fullscreen
  EnterFullscreen ExitFullscreen ToggleFullscreen : VideoMsg
  -- DOM events (from <video> element callbacks)
  TimeUpdated       : String → VideoMsg   -- from onTimeUpdate
  DurationLoaded    : String → VideoMsg   -- from onLoadedMetadata
  VolumeChanged     : String → VideoMsg   -- from onVolumeChange
  MediaEnded        : VideoMsg            -- from onEnded
  MediaError        : String → VideoMsg
  -- Segment events (from Source/SegmentLoader via Cmd callbacks)
  ManifestLoaded    : String → VideoMsg   -- raw m3u8 text
  ManifestError     : String → VideoMsg
  SourceReady       : VideoMsg            -- MediaSource opened
  SourceError       : String → VideoMsg
  LoadNextSegment   : VideoMsg            -- trigger next segment fetch
  SegmentFetched    : ℕ → String → VideoMsg  -- index, base64 data
  SegmentAppended   : ℕ → VideoMsg        -- successfully appended to SourceBuffer
  SegmentError      : ℕ → String → VideoMsg
  AllSegmentsLoaded : VideoMsg            -- all segments appended, end stream
  -- UI
  ControlsShow ControlsHide : VideoMsg
  ControlsActivity  : VideoMsg            -- user interaction → reset hide timer
  SeekBarDragStart SeekBarDragEnd : VideoMsg
  -- Protection (Layer 2+)
  TokenRefreshed    : String → VideoMsg
  KeyLoaded         : String → VideoMsg
  ProtectionError   : String → VideoMsg
```

### PlayerConfig

Consumer-facing configuration record (like SliderConfig):

```agda
record PlayerConfig (M A : Set) : Set where
  field
    -- Data
    pcManifestUrl   : String                    -- HLS manifest URL
    pcAutoplay      : Bool                      -- start playing on load
    pcLoop          : Bool
    pcMuted         : Bool                      -- initial muted state
    pcVolume        : String                    -- initial volume "0.8"
    pcPlaybackRate  : String                    -- initial rate "1"
    -- Layout
    pcLayout        : ControlLayout M A         -- slot assignments (see below)
    pcKeymap        : List (KeyBinding A)       -- keyboard shortcuts
    pcGestures      : List (GestureBinding A)   -- touch gestures
    -- Protection
    pcSignUrl       : Maybe (String → String)   -- Layer 2: URL signing function
    pcDecrypt       : Maybe (String → String)   -- Layer 3: not used in Agda, marker only
    -- Appearance
    pcContainerId   : String                    -- CSS selector for the player container
    pcVideoId       : String                    -- CSS selector for the <video> element
    -- Integration
    pcGetModel      : M → VideoModel            -- lens getter (for zoom)
    pcWrapMsg       : VideoMsg → A              -- lens wrapper (for zoom)

defaultPlayerConfig : ∀ {M A}
  → String                   -- manifest URL
  → (M → VideoModel)         -- getter
  → (VideoMsg → A)           -- wrapper
  → PlayerConfig M A
defaultPlayerConfig url get wrap = record
  { pcManifestUrl  = url
  ; pcAutoplay     = false
  ; pcLoop         = false
  ; pcMuted        = false
  ; pcVolume       = "0.8"
  ; pcPlaybackRate = "1"
  ; pcLayout       = defaultLayout get wrap
  ; pcKeymap       = defaultKeymap wrap
  ; pcGestures     = []
  ; pcSignUrl      = nothing
  ; pcDecrypt      = nothing
  ; pcContainerId  = "agdelte-video-container"
  ; pcVideoId      = "agdelte-video"
  ; pcGetModel     = get
  ; pcWrapMsg      = wrap
  }
```

### ControlLayout

```agda
record ControlLayout (M A : Set) : Set where
  field
    topLeft      : List (Node M A)
    topCenter    : List (Node M A)
    topRight     : List (Node M A)
    left         : List (Node M A)
    right        : List (Node M A)
    bottomLeft   : List (Node M A)
    bottomCenter : List (Node M A)
    bottomRight  : List (Node M A)
```

Default layout provided via `defaultLayout`:
```agda
defaultLayout : ∀ {M A} → (M → VideoModel) → (VideoMsg → A) → ControlLayout M A
defaultLayout get wrap = record
  { topLeft      = []
  ; topCenter    = []
  ; topRight     = []
  ; left         = []
  ; right        = []
  ; bottomLeft   = [ playPauseBtn get wrap , volumeControl get wrap , timeDisplay get wrap ]
  ; bottomCenter = [ seekBar get wrap ]
  ; bottomRight  = [ rateSelector get wrap , fullscreenBtn get wrap ]
  }
```

### KeyBinding / GestureBinding

```agda
record KeyBinding (A : Set) : Set where
  field
    kbKey   : String        -- KeyboardEvent.key value ("Space", "ArrowLeft", etc.)
    kbShift : Bool
    kbCtrl  : Bool
    kbAlt   : Bool
    kbMsg   : A             -- message to dispatch

data GestureType : Set where
  Tap            : GestureType
  DoubleTapLeft  : GestureType    -- double-tap left third of screen
  DoubleTapRight : GestureType    -- double-tap right third of screen
  SwipeH         : GestureType    -- horizontal swipe (seek)
  SwipeVL        : GestureType    -- vertical swipe on left side (brightness)
  SwipeVR        : GestureType    -- vertical swipe on right side (volume)
  Pinch          : GestureType    -- pinch to zoom

record GestureBinding (A : Set) : Set where
  field
    gbGesture : GestureType
    gbMsg     : String → A     -- parameterized by gesture magnitude as String
```

## Playback flow

```
User action
  → Player dispatches VideoMsg
  → update : VideoMsg → VideoModel → VideoModel
  → cmd : VideoMsg → VideoModel → Cmd VideoMsg
      Play  → callMethod pcVideoId "play"
      Pause → callMethod pcVideoId "pause"
      Seek t → setProp pcVideoId "currentTime" t
      SetVolume v → setProp pcVideoId "volume" v
      ...
  → Source requests segment N (via Cmd / Event)
  → SegmentLoader fetches segment (JS postulate)
  → Source appends to SourceBuffer (JS postulate)
  → <video> element renders frames
  → DOM fires timeupdate/volumechange/ended
  → onTimeUpdate, onVolumeChange, onEnded (existing Html helpers) → VideoMsg
  → Controls reflect current state via Binding
```

### Interaction with existing Cmd constructors

The `Cmd` type already has everything needed for basic playback control:

| Action | Cmd constructor | Example |
|---|---|---|
| Play | `callMethod "#my-video" "play"` | Calls `video.play()` |
| Pause | `callMethod "#my-video" "pause"` | Calls `video.pause()` |
| Seek | `setProp "#my-video" "currentTime" "42.5"` | Sets `video.currentTime = 42.5` |
| Volume | `setProp "#my-video" "volume" "0.7"` | Sets `video.volume = 0.7` |
| Mute | `setProp "#my-video" "muted" "true"` | Sets `video.muted = true` |
| Rate | `setProp "#my-video" "playbackRate" "1.5"` | Sets `video.playbackRate = 1.5` |
| Read prop | `getProp "#my-video" "duration" DurationLoaded` | Reads and dispatches |

No new `Cmd` constructors required for basic playback.

### Interaction with existing event helpers (Html.agda)

Already available in `Agdelte.Reactive.Node.Html`:

```agda
onTimeUpdate     : (String → Msg) → Attr Model Msg   -- target.currentTime
onLoadedMetadata : (String → Msg) → Attr Model Msg   -- target.duration
onVolumeChange   : (String → Msg) → Attr Model Msg   -- target.volume
onEnded          : Msg → Attr Model Msg
```

Additional events needed (add to Html.agda or define locally):

```agda
onPlay    = on "play"                  -- fires when playback starts
onPause   = on "pause"                 -- fires when playback pauses
onSeeked  = on "seeked"               -- fires after seek completes
onWaiting = on "waiting"              -- fires when buffering
onError   = onValueFrom "error" "target.error.message"
onProgress = on "progress"            -- fires when new data buffered

-- Buffered end time — target.buffered is a TimeRanges object, needs custom extraction.
-- Define in Util.agda or locally in Player.agda:
onBufferedUpdate : ∀ {Model Msg} → (String → Msg) → Attr Model Msg
onBufferedUpdate = onValueFrom "progress" "target.buffered"
-- Note: onValueFrom extracts via property path, but target.buffered is a TimeRanges,
-- not a string. This needs a custom extraction in reactive.js:
-- Add to renderAttr in reactive.js, special-case for "target.buffered":
--   if (propPath === 'target.buffered') {
--     const buf = e.target.buffered;
--     value = buf.length > 0 ? String(buf.end(buf.length - 1)) : "0";
--   }
```

### SegmentLoader pipeline

SegmentLoader is designed as a chain of steps, each optional and independently
addable:

```
buildURL  →  [signURL]  →  fetch  →  [decrypt]  →  ArrayBuffer
```

Steps in brackets are no-ops by default and activate when protection is enabled.
This means the player works without any protection out of the box, but the
injection points are there for future layers (see PROTECTION.md):

- **signURL** — appends a short-lived authentication token to the segment URL
  (Layer 2).
- **decrypt** — decrypts the fetched segment using a key from the key endpoint
  (Layer 3).
- A/B variant selection (Layer 4) is server-side and transparent to the player —
  SegmentLoader requests the same URL, the server returns the correct variant
  based on the authenticated user.

### Segment format

HLS (`.m4s` segments + `.m3u8` manifest) as the primary format.
Fallback to progressive MP4 for browsers without MSE support (rare).

## JS postulates (Util.agda and SegmentLoader.agda)

Following the pattern from Slider.agda (guardStep, clampMinStr, etc.):

### Time formatting

```agda
-- | Format seconds string "125.7" → "2:05"
postulate formatTime : String → String
{-# COMPILE JS formatTime = function(s) {
  var t = parseFloat(s) || 0;
  var m = Math.floor(t / 60);
  var sec = Math.floor(t % 60);
  return m + ":" + (sec < 10 ? "0" : "") + sec;
} #-}

-- | Format seconds string "125.7" → "02:05:07" (zero-padded, shows hours when ≥ 1h)
postulate formatTimeLong : String → String
{-# COMPILE JS formatTimeLong = function(s) {
  var t = parseFloat(s) || 0;
  var h = Math.floor(t / 3600);
  var m = Math.floor((t % 3600) / 60);
  var sec = Math.floor(t % 60);
  var pad = function(n) { return n < 10 ? "0" + n : "" + n; };
  if (h > 0) return pad(h) + ":" + pad(m) + ":" + pad(sec);
  return pad(m) + ":" + pad(sec);
} #-}

-- | Compute seek bar percentage: currentTime / duration × 100
postulate seekPercent : String → String → String
{-# COMPILE JS seekPercent = function(cur) { return function(dur) {
  var c = parseFloat(cur) || 0, d = parseFloat(dur) || 0;
  if (d <= 0) return "0";
  return String((c / d) * 100);
}; } #-}

-- | Compute buffered percentage: bufferedEnd / duration × 100
postulate bufferedPercent : String → String → String
{-# COMPILE JS bufferedPercent = function(buf) { return function(dur) {
  var b = parseFloat(buf) || 0, d = parseFloat(dur) || 0;
  if (d <= 0) return "0";
  return String((b / d) * 100);
}; } #-}

-- | Clamp volume to [0, 1]
postulate clampVolume : String → String
{-# COMPILE JS clampVolume = function(s) {
  var v = parseFloat(s) || 0;
  return String(Math.max(0, Math.min(1, v)));
} #-}

-- | Add/subtract from time, clamped to [0, duration]
postulate offsetTime : String → String → String → String  -- current, offset, duration
{-# COMPILE JS offsetTime = function(cur) { return function(off) { return function(dur) {
  var c = parseFloat(cur) || 0, o = parseFloat(off) || 0, d = parseFloat(dur) || 0;
  return String(Math.max(0, Math.min(d, c + o)));
}; }; } #-}
```

### MediaSource API (SegmentLoader.agda / Source.agda)

These are opaque JS operations that cannot be expressed in Agda.
They run as `Cmd` side effects or `Event` subscriptions.

```agda
-- Source.agda: MediaSource lifecycle
-- These will be Cmd constructors added to Cmd.agda, or JS-backed postulates
-- called from within executeCmd in reactive.js.

-- Option A: extend Cmd (preferred — keeps side effects in Cmd)
-- Add to Agdelte.Core.Cmd:
--   mediaSourceOpen  : String → (String → A) → Cmd A     -- videoId → onOpen msg
--   appendSegment    : String → String → A → (String → A) → Cmd A
--                    -- videoId, base64/url, onSuccess, onError

-- Option B: JS postulate called inside a Task
-- postulate fetchSegment : String → Task String
-- {-# COMPILE JS fetchSegment = ... #-}
-- Then: attempt (fetchSegment url) (λ { (ok data) → SegmentLoaded n ; (err e) → SegmentError n e })
```

**Recommended: Option B (Task-based).** Reasons:
- `Task` already supports `httpGet` with success/error callbacks.
- SegmentLoader is a chain of async operations — Task composition (`_>>=_`) is natural.
- Avoids polluting the core `Cmd` type with video-specific constructors.
- The `attempt` Cmd constructor bridges Task → Cmd.

New Task primitives (add to `Agdelte.Core.Task` + `executeTask` in reactive.js):

```agda
-- Add to Task.agda data constructors:
  fetchArrayBuffer : String → Task String   -- fetch URL, return as base64 String
  decryptAES128    : String → String → String → Task String
                   -- key (base64), iv (base64), data (base64) → decrypted (base64)
```

```js
// Add to executeTask in reactive.js:
'fetchArrayBuffer': (url, cont) => {
  fetch(url).then(r => {
    if (!r.ok) throw new Error('HTTP ' + r.status);
    return r.arrayBuffer();
  })
  .then(buf => {
    // Convert ArrayBuffer to base64
    const bytes = new Uint8Array(buf);
    let binary = '';
    for (let i = 0; i < bytes.length; i++) binary += String.fromCharCode(bytes[i]);
    cont.pure(btoa(binary));
  })
  .catch(e => cont.fail(e.message));
},
'decryptAES128': (keyB64, ivB64, dataB64, cont) => {
  const toAB = b64 => Uint8Array.from(atob(b64), c => c.charCodeAt(0)).buffer;
  crypto.subtle.importKey('raw', toAB(keyB64), 'AES-CBC', false, ['decrypt'])
    .then(k => crypto.subtle.decrypt({ name: 'AES-CBC', iv: toAB(ivB64) }, k, toAB(dataB64)))
    .then(dec => {
      const bytes = new Uint8Array(dec);
      let binary = '';
      for (let i = 0; i < bytes.length; i++) binary += String.fromCharCode(bytes[i]);
      cont.pure(btoa(binary));
    })
    .catch(e => cont.fail(e.message));
}
```

MediaSource/SourceBuffer management is entirely in JS (reactive.js extension):

```js
// reactive.js — new section: MediaSource management
// Keyed by video element selector, stores { mediaSource, sourceBuffer, queue }
// Exposed as Cmd handlers:
//   'mediaSourceInit': (videoSelector, mimeType, onReady, onError, dispatch) => { ... }
//   'mediaSourceAppend': (videoSelector, base64data, onDone, onError, dispatch) => { ... }
//   'mediaSourceEnd': (videoSelector) => { ... }
```

Corresponding Cmd constructors:
```agda
-- In Cmd.agda (video-specific section):
  mediaSourceInit   : String → String → A → (String → A) → Cmd A
                    -- videoSelector, mimeType, onReady, onError
  mediaSourceAppend : String → String → A → (String → A) → Cmd A
                    -- videoSelector, base64data, onDone, onError
  mediaSourceEnd    : String → Cmd A
                    -- videoSelector — signal end of stream
```

### Manifest parsing (Util.agda)

```agda
-- | Parse .m3u8 manifest, extract segment URLs as JSON array string
postulate parseM3U8 : String → String
{-# COMPILE JS parseM3U8 = function(m3u8Text) {
  // Extract #EXTINF lines and following URLs
  var lines = m3u8Text.split('\n');
  var segments = [];
  for (var i = 0; i < lines.length; i++) {
    if (lines[i].startsWith('#EXTINF:')) {
      if (i + 1 < lines.length && !lines[i+1].startsWith('#')) {
        segments.push(lines[i+1].trim());
      }
    }
  }
  return JSON.stringify(segments);
} #-}

-- | Extract N-th element from JSON array string (0-indexed). Returns "" if out of bounds.
postulate jsonArrayGet : String → ℕ → String
{-# COMPILE JS jsonArrayGet = function(arr) { return function(n) {
  try { var a = JSON.parse(arr); return (n < a.length) ? a[n] : ""; }
  catch(e) { return ""; }
}; } #-}

-- | Get length of JSON array string. Returns 0 on parse error.
postulate jsonArrayLength : String → ℕ
{-# COMPILE JS jsonArrayLength = function(arr) {
  try { return JSON.parse(arr).length; }
  catch(e) { return 0; }
} #-}
```

## UI / Controls (Controls.agda)

The controls layer is fully customizable: layout, appearance, and behavior.
The player ships with sensible defaults but imposes nothing.

### Architecture: headless core + configurable UI

The Player module is **headless** — it exposes state and actions via
`VideoModel` + `VideoMsg`, but has no opinion about what controls exist or
where they are. The Controls module consumes `VideoModel` via `Binding` and
emits `VideoMsg`. This separation means:

- Controls can be rearranged, replaced, or removed without touching Player.
- Custom controls (e.g. a "loop segment" button) can be added by the consumer.
- The player can be used entirely without built-in controls (headless mode),
  driven programmatically or with a fully custom UI.

### Integration via Zoom

Controls.agda defines widgets parametrized by `(M A : Set)` with a getter and
wrapper, using the standard Zoom pattern:

```agda
-- Each control widget follows this signature:
playPauseBtn : ∀ {M A} → (M → VideoModel) → (VideoMsg → A) → Node M A
playPauseBtn get wrap =
  button
    [ class "agdelte-video__play-pause"
    , attrBind "class" (stringBinding (λ m →
        if isPlaying (state (get m))
        then "agdelte-video__play-pause agdelte-video__play-pause--playing"
        else "agdelte-video__play-pause agdelte-video__play-pause--paused"))
    , onClick (wrap TogglePlay)
    , attr "aria-label" "Play/Pause"
    , attr "role" "button"
    , attr "tabindex" "0"
    ]
    [ -- Icon switches based on state via `when`
      when (λ m → isPlaying (state (get m))) pauseIcon
    , when (λ m → not (isPlaying (state (get m)))) playIcon
    ]

seekBar : ∀ {M A} → (M → VideoModel) → (VideoMsg → A) → Node M A
seekBar get wrap =
  div [ class "agdelte-video__seek" ]
    [ -- Buffered progress (background bar)
      div [ class "agdelte-video__seek-buffered"
          , styleBind "width" (stringBinding (λ m → bufferedPercent (buffered (get m)) (duration (get m)) ++ "%"))
          ] []
    , -- Played progress (foreground bar)
      div [ class "agdelte-video__seek-played"
          , styleBind "width" (stringBinding (λ m → seekPercent (currentTime (get m)) (duration (get m)) ++ "%"))
          ] []
    , -- Input range for interaction
      elem "input"
        [ type' "range"
        , class "agdelte-video__seek-input"
        , attr "min" "0"
        , attrBind "max" (stringBinding (λ m → duration (get m)))
        , attr "step" "0.1"
        , valueBind (λ m → currentTime (get m))
        , onInput (wrap ∘ Seek)
        , attr "aria-label" "Seek"
        , attr "aria-valuemin" "0"
        , attrBind "aria-valuemax" (stringBinding (λ m → duration (get m)))
        , attrBind "aria-valuenow" (stringBinding (λ m → currentTime (get m)))
        , attrBind "aria-valuetext" (stringBinding (λ m → formatTime (currentTime (get m))))
        ] []
    ]

volumeControl : ∀ {M A} → (M → VideoModel) → (VideoMsg → A) → Node M A
timeDisplay   : ∀ {M A} → (M → VideoModel) → (VideoMsg → A) → Node M A
fullscreenBtn : ∀ {M A} → (M → VideoModel) → (VideoMsg → A) → Node M A
rateSelector  : ∀ {M A} → (M → VideoModel) → (VideoMsg → A) → Node M A
```

### Top-level player widget

```agda
-- Player.agda exports the main component:
videoPlayer : ∀ {M A} → PlayerConfig M A → Node M A
videoPlayer cfg =
  div [ class "agdelte-video"
      , id' (pcContainerId cfg)
      , attr "tabindex" "0"        -- for keyboard focus
      , onKeyFiltered (keymapKeys cfg) (handleKeypress cfg)
      ]
    [ -- The <video> element (headless — no browser controls)
      video
        [ id' (pcVideoId cfg)
        , class "agdelte-video__media"
        , attr "playsinline" "true"      -- iOS: don't auto-fullscreen
        , onTimeUpdate (pcWrapMsg cfg ∘ TimeUpdated)
        , onLoadedMetadata (pcWrapMsg cfg ∘ DurationLoaded)
        , onVolumeChange (pcWrapMsg cfg ∘ VolumeChanged)
        , onEnded (pcWrapMsg cfg MediaEnded)
        , on "play" (pcWrapMsg cfg (Play))
        , on "pause" (pcWrapMsg cfg (Pause))
        ] []
    , -- Controls overlay
      controlsOverlay cfg
    ]
```

### Layout customization

Controls are organized into **slots** — named regions around the video:

```
┌─────────────────────────────────┐
│ topLeft        topCenter    topRight │
│                                 │
│ left           (video)       right │
│                                 │
│ bottomLeft  bottomCenter bottomRight │
└─────────────────────────────────┘
```

Each slot accepts a list of control widgets. The consumer decides which
controls go into which slots. Default layout provided but overridable.

The `controlsOverlay` renders slots as `div` elements with BEM classes:

```agda
controlsOverlay : ∀ {M A} → PlayerConfig M A → Node M A
controlsOverlay cfg =
  let get = pcGetModel cfg
      layout = pcLayout cfg
  in
  -- Controls shown/hidden via whenT transition (fade in/out)
  whenT (λ m → controlsVisible (get m)) controlsTransition
    (div [ class "agdelte-video__controls"
         , onMouseMove (pcWrapMsg cfg ControlsActivity)  -- reset hide timer on mouse move
         ]
      [ div [ class "agdelte-video__controls-top" ]
          [ div [ class "agdelte-video__slot--top-left" ] (topLeft layout)
          , div [ class "agdelte-video__slot--top-center" ] (topCenter layout)
          , div [ class "agdelte-video__slot--top-right" ] (topRight layout)
          ]
      , div [ class "agdelte-video__controls-bottom" ]
          [ div [ class "agdelte-video__slot--bottom-left" ] (bottomLeft layout)
          , div [ class "agdelte-video__slot--bottom-center" ] (bottomCenter layout)
          , div [ class "agdelte-video__slot--bottom-right" ] (bottomRight layout)
          ]
      ])
```

### CSS classes (BEM)

Following existing convention (`.agdelte-slider`, `.agdelte-accordion`, etc.):

```
.agdelte-video                           — container
.agdelte-video__media                    — <video> element
.agdelte-video__controls                 — overlay container
.agdelte-video__controls--visible        — shown (opacity 1)
.agdelte-video__controls--hidden         — auto-hidden (opacity 0, transition)
.agdelte-video__slot--top-left           — slot region
.agdelte-video__slot--bottom-center      — slot region
.agdelte-video__play-pause               — play/pause button
.agdelte-video__play-pause--playing      — playing state
.agdelte-video__play-pause--paused       — paused state
.agdelte-video__seek                     — seek bar container
.agdelte-video__seek-input               — range input (transparent, above)
.agdelte-video__seek-played              — played portion (foreground bar)
.agdelte-video__seek-buffered            — buffered portion (background bar)
.agdelte-video__volume                   — volume control container
.agdelte-video__volume-slider            — volume range input
.agdelte-video__volume-icon              — speaker icon
.agdelte-video__volume-icon--muted       — muted state
.agdelte-video__time                     — time display (current / duration)
.agdelte-video__fullscreen               — fullscreen toggle
.agdelte-video__fullscreen--active       — currently fullscreen
.agdelte-video__rate                     — playback rate selector
.agdelte-video__loading                  — buffering spinner overlay
```

CSS module (`src/Agdelte/Css/Controls/Video.agda`) follows the same pattern
as `Css/Controls/Slider.agda` — uses `Stylesheet`, `Rule`, `∶` operator:

```agda
module Agdelte.Css.Controls.Video where

open import Agdelte.Css using (Stylesheet; rule; _∶_; var)

videoCSS : Stylesheet
videoCSS =
  rule ".agdelte-video"
    [ "position" ∶ "relative"
    , "overflow" ∶ "hidden"
    , "background" ∶ "#000"
    , "border-radius" ∶ var "--agdelte-video-border-radius"
    ]
  ∷ rule ".agdelte-video__media"
    [ "width" ∶ "100%"
    , "height" ∶ "100%"
    , "display" ∶ "block"
    ]
  ∷ rule ".agdelte-video__controls"
    [ "position" ∶ "absolute"
    , "bottom" ∶ "0"
    , "left" ∶ "0"
    , "right" ∶ "0"
    , "padding" ∶ var "--agdelte-video-controls-padding"
    , "background" ∶ var "--agdelte-video-controls-bg"
    , "color" ∶ var "--agdelte-video-controls-color"
    , "transition" ∶ var "--agdelte-video-controls-transition"
    , "opacity" ∶ "1"
    ]
  ∷ rule ".agdelte-video__controls--hidden"
    [ "opacity" ∶ "0"
    , "pointer-events" ∶ "none"
    ]
  ∷ rule ".agdelte-video__seek"
    [ "position" ∶ "relative"
    , "height" ∶ var "--agdelte-video-seek-height"
    , "cursor" ∶ "pointer"
    ]
  ∷ rule ".agdelte-video__seek-played"
    [ "height" ∶ "100%"
    , "background" ∶ var "--agdelte-video-progress-color"
    , "border-radius" ∶ var "--agdelte-video-border-radius"
    ]
  ∷ rule ".agdelte-video__seek-buffered"
    [ "position" ∶ "absolute"
    , "height" ∶ "100%"
    , "background" ∶ var "--agdelte-video-buffered-color"
    ]
  ∷ []
```

CSS custom properties (defaults, overridable by consumer themes):

```
--agdelte-video-controls-bg         : rgba(0,0,0,0.7)
--agdelte-video-controls-color      : #fff
--agdelte-video-progress-color      : var(--agdelte-primary)
--agdelte-video-buffered-color      : rgba(255,255,255,0.3)
--agdelte-video-controls-padding    : 8px
--agdelte-video-controls-transition : opacity 0.3s ease
--agdelte-video-icon-size           : 24px
--agdelte-video-seek-height         : 4px
--agdelte-video-seek-thumb-size     : 12px
--agdelte-video-border-radius       : 4px
```

### Appearance customization

- **CSS custom properties** for colors, sizes, spacing, border-radius,
  opacity, font, icon size, etc. No hardcoded visual values.
- **Custom icons** — each control accepts an optional icon override
  (SVG node or image URL).
- **Animations/transitions** — configurable via CSS or Agdelte animation
  primitives (show/hide controls, hover effects, seek bar thumb).
  Controls show/hide uses `whenT` with a `Transition`:
  ```agda
  controlsTransition : Transition
  controlsTransition = mkTransition
    "agdelte-video__controls--visible"
    "agdelte-video__controls--hidden"
    300  -- ms
  ```
- **Themes** — a theme is just a set of CSS custom property values.
  Multiple themes can be predefined; the consumer picks or provides their own.

### Keyboard bindings

All keyboard shortcuts are configurable via a keymap — a mapping from
key combination to player action:

```agda
defaultKeymap : ∀ {A} → (VideoMsg → A) → List (KeyBinding A)
defaultKeymap wrap =
    mkKB "Space"      false false false (wrap TogglePlay)
  ∷ mkKB "ArrowLeft"  false false false (wrap (Seek "-5"))    -- relative seek via offsetTime
  ∷ mkKB "ArrowRight" false false false (wrap (Seek "+5"))
  ∷ mkKB "ArrowLeft"  true  false false (wrap (Seek "-10"))   -- shift+arrow
  ∷ mkKB "ArrowRight" true  false false (wrap (Seek "+10"))
  ∷ mkKB "m"          false false false (wrap ToggleMute)
  ∷ mkKB "f"          false false false (wrap ToggleFullscreen)
  ∷ mkKB "ArrowUp"    false false false (wrap (SetVolume "+0.05"))
  ∷ mkKB "ArrowDown"  false false false (wrap (SetVolume "-0.05"))
  ∷ mkKB "Escape"     false false false (wrap ExitFullscreen)
  ∷ []
```

Keyboard handling uses the existing `onKeyFiltered` Attr constructor to filter
relevant keys, then pattern-matches on `KeyboardEvent` fields (key, shift, ctrl, alt)
in the update function. This avoids global `Sub.onKeyDown` — keys only captured
when the player container has focus.

### Touch / pointer gestures

Gestures are also configurable as a gesture map:

- Tap → togglePlay (default)
- Double-tap left/right → seek ±10s
- Swipe horizontal → seek
- Swipe vertical (right side) → volume
- Swipe vertical (left side) → brightness (if supported)
- Pinch → zoom (optional)

Each gesture can be rebound or disabled.

Gesture detection is a JS postulate that interprets touch events and returns
a `GestureType` + magnitude. The Agda side uses `onTouchStart`/`onTouchEnd`
(already in Html.agda) and delegates interpretation:

```agda
postulate classifyGesture : String → String → String → String → String
-- startX, startY, endX, endY → JSON: {"gesture": "swipe-h", "magnitude": "120"}
```

### Responsive behavior

- Controls adapt to container width (not viewport) via container queries.
- Below configurable breakpoints, controls can collapse into a minimal set
  or switch to a compact layout.
- Touch-friendly hit targets on small sizes.

### Accessibility

Following patterns from `Agdelte.Svg.Accessibility`:

- `attr "role" "region"` on the player container with `attr "aria-label" "Video player"`
- `attr "role" "slider"` on seek bar with `aria-valuemin`, `aria-valuemax`,
  `aria-valuenow`, `aria-valuetext` (time-formatted)
- `attr "role" "button"` on play/pause, fullscreen, mute
- `attr "aria-pressed"` on toggle buttons (mute, fullscreen)
- `attr "aria-live" "polite"` on time display for screen reader updates
- `attr "tabindex" "0"` on the container for keyboard focus capture
- Focus visible indicator via `:focus-visible` CSS (no outline suppression)

## State management

Reactive state via existing `Binding` primitives. All model fields exposed
as `stringBinding` / `boolBinding` for efficient change detection:

```agda
-- Binding examples for Controls:
isPlayingBind : ∀ {M} → (M → VideoModel) → Binding M String
isPlayingBind get = boolBinding (λ m → isPlaying (state (get m)))

currentTimeFormatted : ∀ {M} → (M → VideoModel) → Binding M String
currentTimeFormatted get = stringBinding (λ m → formatTime (currentTime (get m)))

seekPosition : ∀ {M} → (M → VideoModel) → Binding M String
seekPosition get = stringBinding (λ m → seekPercent (currentTime (get m)) (duration (get m)) ++ "%")
```

## Events (subscriptions)

Using existing `Event` constructors from `Agdelte.Core.Event`:

```agda
videoSubs : VideoModel → Event VideoMsg
videoSubs model =
  -- Auto-hide controls after 3s of inactivity (when playing and visible)
  (if isPlaying (state model) ∧ controlsVisible model
   then sub (timeout 3000 ControlsHide)
   else never)
```

Standard DOM events: `play`, `pause`, `seeked`, `ended`, `error`,
`timeupdate`, `volumechange` — handled via `Attr` event handlers on `<video>`,
not via `Event` subscriptions.

Segment loading is driven by `Cmd` chains, not `Event` subscriptions:
`SourceReady → loadSegmentCmd 0 → SegmentFetched → mediaSourceAppend →
SegmentAppended → loadSegmentCmd 1 → ...`. Each step triggers the next via
`mkVideoCmd`, forming a self-sustaining pipeline without polling.

## Source.agda — MediaSource management

Source.agda doesn't contain business logic — the segment loading pipeline is
driven by `mkVideoCmd` (above) via Cmd chains. Source.agda provides:

1. **Init helper** — called once when the player loads:
```agda
-- Request manifest, init MediaSource. Called from the consumer's cmd on init.
initVideoSource : ∀ {M A} → PlayerConfig M A → Cmd VideoMsg
initVideoSource cfg =
  httpGet (pcManifestUrl cfg) ManifestLoaded ManifestError
```

2. **Segment URL resolution** — uses `jsonArrayGet` + `pcSignUrl` (see `loadSegmentCmd` above).

3. **Buffer state query** (via JS postulate) — to check buffered range:
```agda
-- | Get the furthest buffered time for the video element
postulate getBufferedEnd : String → String   -- videoSelector → seconds as String
{-# COMPILE JS getBufferedEnd = function(sel) {
  var el = document.querySelector(sel);
  if (el && el.buffered.length > 0) return String(el.buffered.end(el.buffered.length - 1));
  return "0";
} #-}
```

## SegmentLoader.agda — fetch pipeline

SegmentLoader is the `Task`-based pipeline from URL to data. The core function:

```agda
-- | Full pipeline: build URL → [sign] → fetch → [decrypt] → base64 data
loadSegment : ∀ {M A} → PlayerConfig M A → String → Task String
loadSegment cfg url =
  let signedUrl = case pcSignUrl cfg of
                    nothing → url
                    just sign → sign url
  in fetchArrayBuffer signedUrl >>= λ data →
     case pcDecrypt cfg of
       nothing → pure data
       just decrypt → pure (decrypt data)   -- Layer 3: decryption step
```

Note: `pcDecrypt` is a `Maybe (String → String)` — a JS postulate provided
by the consumer. For AES-128, the consumer provides:
```agda
postulate decryptAES128JS : String → String → String  -- key, data → decrypted
{-# COMPILE JS decryptAES128JS = function(key) { return function(data) {
  // Uses SubtleCrypto — synchronous wrapper over cached key
  return decryptWithCachedKey(key, data);
}; } #-}
```

When Task-based async decryption is needed instead (key fetch + decrypt),
replace `pcDecrypt` with a `Task`-based pipeline — see PROTECTION.md Layer 3.

## update function

`updateVideo` and `videoCmd` are parametrized by `PlayerConfig` — the config
is captured in a closure when constructing the `ReactiveApp`, not passed per-message.

```agda
-- Update closes over config for access to pcAutoplay, pcVideoId, etc.
mkUpdateVideo : ∀ {M A} → PlayerConfig M A → VideoMsg → VideoModel → VideoModel
mkUpdateVideo cfg = go
  where
  go : VideoMsg → VideoModel → VideoModel
  go Play m             = record m { state = Playing ; controlsVisible = true }
  go Pause m            = record m { state = Paused ; controlsVisible = true }
  go TogglePlay m       = record m { state = if isPlaying (state m) then Paused else Playing }
  go (Seek _) m         = m  -- actual seek is a Cmd; time arrives via TimeUpdated
  go (SetVolume v) m    = record m { volume = clampVolume v }
  go ToggleMute m       = record m { muted = not (muted m) }
  go (SetRate r) m      = record m { playbackRate = r }
  go (TimeUpdated t) m  = record m { currentTime = t }
  go (DurationLoaded d) m = record m { duration = d
                                      ; state = if pcAutoplay cfg then Loading else Paused }
  go (VolumeChanged v) m  = record m { volume = v }
  go MediaEnded m         = record m { state = if pcLoop cfg then Playing else Ended }
  go (MediaError e) m     = record m { state = Error ; error = just e }
  go (ManifestLoaded raw) m =
    let urls = parseM3U8 raw
        count = jsonArrayLength urls
    in record m { segmentUrls = urls ; totalSegments = count ; state = Loading }
  go (ManifestError e) m  = record m { state = Error ; error = just e }
  go SourceReady m        = record m { sourceReady = true }
  go (SourceError e) m    = record m { state = Error ; error = just e }
  go (SegmentFetched _ _) m = m  -- data is in Cmd, not model
  go (SegmentAppended n) m  = record m { currentSegment = suc n }
  go AllSegmentsLoaded m    = m  -- mediaSourceEnd called in cmd
  go (SegmentError _ e) m   = record m { state = Error ; error = just e }
  go ControlsShow m       = record m { controlsVisible = true }
  go ControlsHide m       = record m { controlsVisible = false }
  go ControlsActivity m   = record m { controlsVisible = true }
  go _ m                  = m

mkVideoCmd : ∀ {M A} → PlayerConfig M A → VideoMsg → VideoModel → Cmd VideoMsg
mkVideoCmd cfg = go
  where
  vid = pcVideoId cfg
  go : VideoMsg → VideoModel → Cmd VideoMsg
  -- Playback
  go Play _                 = callMethod vid "play"
  go Pause _                = callMethod vid "pause"
  go TogglePlay m           = if isPlaying (state m) then callMethod vid "pause"
                              else callMethod vid "play"
  go (Seek t) m             = setProp vid "currentTime" (offsetTime (currentTime m) t (duration m))
  go (SetVolume v) _        = setProp vid "volume" (clampVolume v)
  go ToggleMute m           = setProp vid "muted" (if muted m then "false" else "true")
  go (SetRate r) _          = setProp vid "playbackRate" r
  go ToggleFullscreen _     = callMethod (pcContainerId cfg) "requestFullscreen"

  -- Source lifecycle (see Source.agda section below)
  go (DurationLoaded _) m   =
    -- Manifest already loaded → init MediaSource
    if sourceReady m then ε
    else mediaSourceInit vid "video/mp4; codecs=\"avc1.42E01E, mp4a.40.2\""
           SourceReady SourceError
  go SourceReady m           =
    -- MediaSource ready → start loading first segment
    if totalSegments m > 0 then loadSegmentCmd cfg m 0 else ε
  go (SegmentFetched n base64data) _ =
    mediaSourceAppend vid base64data (SegmentAppended n) (λ e → SegmentError n e)
  go (SegmentAppended n) m  =
    -- Load next segment, or end stream if all loaded
    let next = suc n
    in if next < totalSegments m then loadSegmentCmd cfg m next
       else ε
  go AllSegmentsLoaded _    = mediaSourceEnd vid
  go LoadNextSegment m      = loadSegmentCmd cfg m (currentSegment m)

  -- Manifest loading (on init)
  go (ManifestLoaded _) _   = ε  -- model updated in update; cmd for init segment:
                              -- mediaSourceInit happens after DurationLoaded
  -- Loop
  go MediaEnded m           = if pcLoop cfg then callMethod vid "play" <> setProp vid "currentTime" "0" else ε

  go _ _                    = ε

-- | Load a single segment: fetch → SegmentFetched | SegmentError
loadSegmentCmd : ∀ {M A} → PlayerConfig M A → VideoModel → ℕ → Cmd VideoMsg
loadSegmentCmd cfg m idx =
  let url = jsonArrayGet (segmentUrls m) idx
      signedUrl = case pcSignUrl cfg of
                    nothing → url
                    just sign → sign url
  in attempt (fetchArrayBuffer signedUrl)
       (λ { (ok data)  → SegmentFetched idx data
          ; (err msg)  → SegmentError idx msg })
```

## Protection integration points

The player is designed so that content protection (see PROTECTION.md) can be
added later without rewriting core playback logic:

| Protection layer | Where it hooks in | Player-side change |
|---|---|---|
| No direct URL (Layer 1) | Architecture | None — already MediaSource-based |
| Signed URLs (Layer 2) | SegmentLoader `signURL` step | `pcSignUrl` in PlayerConfig |
| AES-128 encryption (Layer 3) | SegmentLoader `decrypt` step via Task | New Task: `decryptAES128` |
| A/B watermarking (Layer 4) | Server-side only | None — transparent to player |
| UI deterrence (Layer 5) | Player / Controls | `on "contextmenu"` + devtools detection postulate |

## Runtime extensions (reactive.js)

New code needed in `runtime/reactive.js`:

1. **MediaSource management** — `executeCmd` handlers for `mediaSourceInit`,
   `mediaSourceAppend`, `mediaSourceEnd`. Keyed by video selector, stores
   `{ mediaSource, sourceBuffer, appendQueue }` per player instance.
   Cleanup via scope destruction (existing `destroyScope` pattern).

2. **Fullscreen toggle** — `callMethod` already exists but `requestFullscreen`
   returns a Promise and may need vendor prefix. Extend `callMethod` to handle
   Promises silently, or add a dedicated `toggleFullscreen` Cmd handler.

3. **ArrayBuffer fetch** in `executeTask` — new case for `fetchArrayBuffer` Task.

4. **AES-128 decryption** in `executeTask` — uses `crypto.subtle.decrypt`.

All additions follow the existing pattern: Scott-encoded Cmd/Task → `executeCmd`/
`executeTask` switch → browser API call → dispatch callback.

## Consumer usage example

```agda
-- In the consumer's app:

record AppModel : Set where
  field
    videoState : VideoModel
    -- ...other app state...

data AppMsg : Set where
  VideoAction : VideoMsg → AppMsg
  -- ...other app messages...

-- Config defined once, used by update, cmd, and template
appVideoConfig : PlayerConfig AppModel AppMsg
appVideoConfig = defaultPlayerConfig
    "https://example.com/video/manifest.m3u8"
    videoState       -- getter: AppModel → VideoModel
    VideoAction      -- wrapper: VideoMsg → AppMsg

-- Update: apply video update to the videoState field
updateApp : AppMsg → AppModel → AppModel
updateApp (VideoAction vm) m =
  record m { videoState = mkUpdateVideo appVideoConfig vm (videoState m) }
updateApp _ m = m

-- Cmd: map VideoMsg commands to AppMsg
-- Note: Cmd has no mapCmd in the current codebase. Two options:
-- (a) Add `mapCmd : (A → B) → Cmd A → Cmd B` to Cmd.agda (recommended).
--     Implementation: structural recursion over Cmd constructors, wrapping callbacks.
-- (b) Define videoCmd directly in terms of AppMsg by using pcWrapMsg in mkVideoCmd.
--     This is what happens naturally since mkVideoCmd already uses the cfg's selectors.
--
-- Option (b) is simpler — the cmd function returns Cmd AppMsg directly:

cmdApp : AppMsg → AppModel → Cmd AppMsg
cmdApp (VideoAction vm) m =
  -- mkVideoCmd returns Cmd VideoMsg; we need Cmd AppMsg.
  -- Since Cmd constructors take callbacks (String → A), we can wrap them.
  -- Add to Cmd.agda:
  --   mapCmd : (A → B) → Cmd A → Cmd B
  --   {-# COMPILE JS mapCmd = ... #-}  (recursively wraps all callbacks)
  mapCmd VideoAction (mkVideoCmd appVideoConfig vm (videoState m))
cmdApp _ _ = ε

-- Template
template : Node AppModel AppMsg
template =
  div [ class "app" ]
    [ videoPlayer appVideoConfig ]

-- Subscriptions
subsApp : AppModel → Event AppMsg
subsApp m = mapE VideoAction (videoSubs (videoState m))
-- mapE already exists in Agdelte.Core.Event

-- Full app
app : ReactiveApp AppModel AppMsg
app = record
  { init     = record { videoState = defaultVideoModel }
  ; update   = updateApp
  ; template = template
  ; cmd      = cmdApp
  ; subs     = subsApp
  }
```

### Required addition: `mapCmd`

`Cmd` currently has no `map` function. Add to `Agdelte.Core.Cmd`:

```agda
mapCmd : ∀ {A B} → (A → B) → Cmd A → Cmd B
mapCmd f ε = ε
mapCmd f (c₁ <> c₂) = mapCmd f c₁ <> mapCmd f c₂
mapCmd f (delay n a) = delay n (f a)
mapCmd f (httpGet url ok err) = httpGet url (f ∘ ok) (f ∘ err)
mapCmd f (httpPost url body ok err) = httpPost url body (f ∘ ok) (f ∘ err)
mapCmd f (attempt task handler) = attempt task (f ∘ handler)
mapCmd f (callMethod sel method) = callMethod sel method
mapCmd f (setProp sel prop val) = setProp sel prop val
mapCmd f (getProp sel prop handler) = getProp sel prop (f ∘ handler)
mapCmd f (focus sel) = focus sel
mapCmd f (blur sel) = blur sel
-- ... (same pattern for all constructors: wrap callbacks, pass through pure args)
-- Constructors without callbacks (scrollTo, writeClipboard, etc.) pass through unchanged.

-- In reactive.js: mapCmd is structural — no runtime change needed.
-- MAlonzo/JS compilation handles it automatically since it's pure recursion.
```

## Future considerations

- Adaptive bitrate (ABR) — quality switching based on bandwidth.
  Needs bandwidth estimation (moving average of segment download times)
  and manifest with multiple quality levels. ABR logic in Source.agda,
  quality selection in SegmentLoader.agda.
- Subtitles / multiple audio tracks — WebVTT parsing (JS postulate),
  track selection UI in Controls.
- Picture-in-picture — `callMethod "#video" "requestPictureInPicture"`.
