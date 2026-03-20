# Agdelte.Html.Controls.Video

MediaSource-based video player with segmented delivery.
Headless `<video>` core with a configurable controls overlay.
All components return `Node M A` and compose with other Agdelte elements.

## Quick Start

```agda
open import Agdelte.Html.Controls  -- re-exports Video.Player

-- In your app:
videoPlayer (defaultPlayerConfig "manifest.m3u8" getVideoState VideoAction)
```

`defaultPlayerConfig` gives you the default layout (play/pause, seek, volume,
time display, rate selector, fullscreen), the default keymap, and no content
protection. Override individual fields with record update syntax.

## Types

### PlayerState

```agda
data PlayerState : Set where
  Idle Loading Playing Paused Ended Error : PlayerState
```

| State     | Meaning |
|-----------|---------|
| `Idle`    | Initial state, no media loaded |
| `Loading` | Manifest fetched, segments downloading |
| `Playing` | Media is playing |
| `Paused`  | Media is paused |
| `Ended`   | Playback reached the end |
| `Error`   | Unrecoverable error (absorbing -- playback commands are ignored) |

Helper predicates: `isPlaying`, `isPaused`, `eqState`.

### VideoModel

```agda
record VideoModel : Set where
  field
    state           : PlayerState
    currentTime     : String         -- seconds, from DOM
    duration        : String         -- seconds, from DOM
    volume          : String         -- [0..1]
    muted           : Bool
    fullscreen      : Bool
    buffered        : String         -- furthest buffered position (seconds)
    playbackRate    : String         -- "1" default
    error           : Maybe String   -- last error message
    controlsVisible : Bool           -- whether controls overlay is shown
    currentSegment  : N              -- index of next segment to load
    totalSegments   : N              -- total segment count from manifest
    segmentUrls     : String         -- JSON array of segment URLs
    manifestUrl     : String
    sourceReady     : Bool           -- MediaSource is open
```

`defaultVideoModel` initialises all fields to safe defaults (Idle, volume 0.8,
controls visible, no error).

### VideoMsg

Messages grouped by category:

**Playback**

| Constructor | Payload | Description |
|-------------|---------|-------------|
| `Play` | -- | Start playback |
| `Pause` | -- | Pause playback |
| `TogglePlay` | -- | Toggle play/pause |
| `Seek` | `String` | Relative offset (`"-5"`, `"+10"`) |
| `SeekTo` | `String` | Absolute position (`"42.5"`) |
| `SetVolume` | `String` | Absolute volume (`"0.5"`) |
| `AdjustVolume` | `String` | Relative volume (`"+0.05"`, `"-0.1"`) |
| `ToggleMute` | -- | Toggle mute |
| `SetRate` | `String` | Set playback rate (`"1.5"`) |
| `EnterFullscreen` | -- | Enter fullscreen |
| `ExitFullscreen` | -- | Exit fullscreen |
| `ToggleFullscreen` | -- | Toggle fullscreen |

**DOM events** (fired by the `<video>` element)

| Constructor | Payload | Description |
|-------------|---------|-------------|
| `TimeUpdated` | `String` | Current time changed |
| `DurationLoaded` | `String` | Duration metadata loaded |
| `VolumeChanged` | `String` | Volume changed externally |
| `MediaEnded` | -- | Playback reached end |
| `MediaError` | `String` | Browser-level media error |

**Segment events**

| Constructor | Payload | Description |
|-------------|---------|-------------|
| `ManifestLoaded` | `String` | Raw M3U8 manifest text |
| `ManifestError` | `String` | Manifest fetch failed |
| `SourceReady` | -- | MediaSource opened |
| `SourceError` | `String` | MediaSource failed |
| `LoadNextSegment` | -- | Request next segment |
| `SegmentFetched` | `N`, `String` | Segment index + base64 data |
| `SegmentAppended` | `N` | Segment appended to buffer |
| `SegmentError` | `N`, `String` | Segment fetch/append failed |
| `AllSegmentsLoaded` | -- | All segments appended |
| `BufferedUpdated` | `String` | Furthest buffered time |

**UI**

| Constructor | Description |
|-------------|-------------|
| `ControlsShow` | Show controls overlay |
| `ControlsHide` | Hide controls overlay |
| `ControlsActivity` | Reset auto-hide timer |

**Protection** (future -- see Future section)

| Constructor | Payload | Description |
|-------------|---------|-------------|
| `TokenRefreshed` | `String` | New auth token |
| `KeyLoaded` | `String` | Decryption key |
| `ProtectionError` | `String` | Protection layer error |

### PlayerConfig

```agda
record PlayerConfig (M A : Set) : Set where
  field
    pcManifestUrl   : String                     -- HLS manifest URL
    pcAutoplay      : Bool                       -- auto-play on duration load
    pcLoop          : Bool                       -- loop on end
    pcMuted         : Bool                       -- start muted
    pcVolume        : String                     -- initial volume [0..1]
    pcPlaybackRate  : String                     -- initial rate
    pcLayout        : ControlLayout M A          -- controls slot layout
    pcKeymap        : List (KeyBinding A)        -- keyboard shortcuts
    pcGestures      : List (GestureBinding A)    -- touch gestures
    pcSignUrl       : Maybe (String -> String)   -- URL signing function
    pcContainerId   : String                     -- container DOM id
    pcVideoId       : String                     -- <video> DOM id
    pcGetModel      : M -> VideoModel            -- model getter (zoom)
    pcWrapMsg       : VideoMsg -> A              -- message wrapper (zoom)
```

`defaultPlayerConfig url get wrap` produces a config with autoplay off,
loop off, volume 0.8, the default layout and keymap, no gestures, no URL
signing, and standard DOM ids.

`initVideoModel cfg` creates an initial `VideoModel` applying config values
(volume, muted, rate, manifest URL).

### ControlLayout

8-region slot system for positioning controls over the video:

```
+------------+---------------+-------------+
|  topLeft   |   topCenter   |  topRight   |
+------------+---------------+-------------+
|   left     |               |   right     |
+------------+---------------+-------------+
| bottomLeft | bottomCenter  | bottomRight |
+------------+---------------+-------------+
```

```agda
record ControlLayout (M A : Set) : Set where
  field
    topLeft topCenter topRight       : List (Node M A)
    left right                       : List (Node M A)
    bottomLeft bottomCenter bottomRight : List (Node M A)
```

Each slot holds a list of `Node M A` widgets. `emptyLayout` provides all-empty
slots. `defaultLayout` places play/pause + volume + time in `bottomLeft`,
seek bar in `bottomCenter`, rate selector + fullscreen in `bottomRight`.

### KeyBinding

```agda
record KeyBinding (A : Set) : Set where
  field
    kbKey   : String   -- key name (e.g. "ArrowLeft", " ", "m")
    kbShift : Bool
    kbCtrl  : Bool
    kbAlt   : Bool
    kbMsg   : A        -- message to dispatch
```

### GestureBinding

```agda
data GestureType : Set where
  Tap DoubleTapLeft DoubleTapRight : GestureType
  SwipeH SwipeVL SwipeVR Pinch    : GestureType

record GestureBinding (A : Set) : Set where
  field
    gbGesture : GestureType
    gbMsg     : String -> A   -- receives gesture magnitude as string
```

## Controls

Individual widgets, each taking a getter and wrapper for zoom composition:

```agda
playPauseBtn  : (M -> VideoModel) -> (VideoMsg -> A) -> Node M A
seekBar       : (M -> VideoModel) -> (VideoMsg -> A) -> Node M A
volumeControl : (M -> VideoModel) -> (VideoMsg -> A) -> Node M A
timeDisplay   : (M -> VideoModel) -> (VideoMsg -> A) -> Node M A
fullscreenBtn : (M -> VideoModel) -> (VideoMsg -> A) -> Node M A
rateSelector  : (M -> VideoModel) -> (VideoMsg -> A) -> Node M A
```

### defaultLayout

```agda
defaultLayout : (M -> VideoModel) -> (VideoMsg -> A) -> ControlLayout M A
```

Places widgets as follows:

| Slot | Contents |
|------|----------|
| `bottomLeft` | `playPauseBtn`, `volumeControl`, `timeDisplay` |
| `bottomCenter` | `seekBar` |
| `bottomRight` | `rateSelector`, `fullscreenBtn` |
| all others | empty |

### controlsOverlay

```agda
controlsOverlay : PlayerConfig M A -> Node M A
```

Renders all 8 layout slots in a `div.agdelte-video__controls`. Uses a
transition (`controlsTransition`, 300ms) to fade in/out based on
`controlsVisible`. Mouse movement over the overlay dispatches
`ControlsActivity`.

## State Machine

### mkUpdateVideo

```agda
mkUpdateVideo : PlayerConfig M A -> VideoMsg -> VideoModel -> VideoModel
```

Key transitions:

- `Play` / `Pause` / `TogglePlay` -- blocked when `state = Error`
- `DurationLoaded` -- sets state to `Playing` if `pcAutoplay`, else `Paused`
- `MediaEnded` -- loops back to `Playing` if `pcLoop`, else `Ended`
- `ManifestLoaded` -- parses M3U8, sets `segmentUrls`/`totalSegments`, transitions to `Loading`; errors on empty manifest
- `SourceReady` -- marks `sourceReady = true`
- `SegmentAppended n` -- advances `currentSegment` to `suc n`
- Any error constructor -- sets `state = Error` with message

### mkVideoCmd

```agda
mkVideoCmd : PlayerConfig M A -> VideoMsg -> VideoModel -> Cmd VideoMsg
```

Side effects per message:

- `Play` / `Pause` -- calls `.play()` / `.pause()` on the video element
- `Seek` / `SeekTo` -- sets `currentTime` property (clamped)
- `SetVolume` / `AdjustVolume` -- sets `volume` property (clamped to [0,1])
- `ToggleMute` -- sets `muted` property
- `SetRate` -- sets `playbackRate` property
- `EnterFullscreen` / `ToggleFullscreen` -- calls `requestFullscreen` on container
- `ExitFullscreen` -- calls `document.exitFullscreen`
- `ManifestLoaded` -- initialises MediaSource with codec string
- `SourceReady` -- loads first segment
- `SegmentFetched` -- appends base64 data to MediaSource buffer
- `SegmentAppended n` -- loads next segment or calls `mediaSourceEnd`
- `MediaEnded` + loop -- calls `.play()` and resets `currentTime` to `"0"`

### videoSubs

```agda
videoSubs : VideoModel -> Event VideoMsg
```

When `state = Playing` and `controlsVisible = true`, emits `ControlsHide`
after 3000ms. Otherwise `never`.

### initVideoSource

```agda
initVideoSource : PlayerConfig M A -> Cmd VideoMsg
```

Fetches the manifest URL (with optional URL signing). Call this from your
app's init command.

## Keyboard Shortcuts

Default keymap (`defaultKeymap wrap`):

| Key | Shift | Action |
|-----|-------|--------|
| Space | -- | `TogglePlay` |
| ArrowLeft | -- | `Seek "-5"` |
| ArrowRight | -- | `Seek "+5"` |
| ArrowLeft | Shift | `Seek "-10"` |
| ArrowRight | Shift | `Seek "+10"` |
| ArrowUp | -- | `AdjustVolume "+0.05"` |
| ArrowDown | -- | `AdjustVolume "-0.05"` |
| m | -- | `ToggleMute` |
| f | -- | `ToggleFullscreen` |
| Escape | -- | `ExitFullscreen` |

## Integration

Embed in a larger app using the standard zoom pattern:

```agda
-- Your app model contains a VideoModel field
record AppModel : Set where
  field
    videoState : VideoModel
    -- ...other fields

-- Getter and wrapper
getVideo : AppModel -> VideoModel
getVideo = videoState

data AppMsg : Set where
  VideoAction : VideoMsg -> AppMsg
  -- ...other messages

-- Build the player
myPlayer : Node AppModel AppMsg
myPlayer = videoPlayer (defaultPlayerConfig "content/manifest.m3u8" getVideo VideoAction)

-- In your update function, delegate:
update (VideoAction vmsg) model =
  let vm  = getVideo model
      vm' = mkUpdateVideo cfg vmsg vm
  in record model { videoState = vm' }

-- In your cmd function, delegate and map:
cmd (VideoAction vmsg) model =
  mapCmd VideoAction (mkVideoCmd cfg vmsg (getVideo model))

-- In your subscriptions, delegate and map:
subs model = mapE VideoAction (videoSubs (getVideo model))

-- On init, fetch the manifest:
initCmd = mapCmd VideoAction (initVideoSource cfg)
```

## CSS Classes

All classes follow BEM convention under the `.agdelte-video` block:

| Class | Element |
|-------|---------|
| `.agdelte-video` | Root container |
| `.agdelte-video__media` | `<video>` element |
| `.agdelte-video__controls` | Controls overlay |
| `.agdelte-video__controls--visible` | Controls fade-in |
| `.agdelte-video__controls--hidden` | Controls fade-out |
| `.agdelte-video__controls-top` | Top row |
| `.agdelte-video__controls-middle` | Middle row |
| `.agdelte-video__controls-bottom` | Bottom row |
| `.agdelte-video__slot--top-left` | Slot (same pattern for all 8) |
| `.agdelte-video__play-pause` | Play/pause button |
| `.agdelte-video__play-pause--playing` | Playing modifier |
| `.agdelte-video__play-pause--paused` | Paused modifier |
| `.agdelte-video__seek` | Seek bar container |
| `.agdelte-video__seek-buffered` | Buffered progress bar |
| `.agdelte-video__seek-played` | Played progress bar |
| `.agdelte-video__seek-input` | Range input |
| `.agdelte-video__volume` | Volume group |
| `.agdelte-video__volume-icon` | Mute button |
| `.agdelte-video__volume-icon--muted` | Muted modifier |
| `.agdelte-video__volume-slider` | Volume range input |
| `.agdelte-video__time` | Time display |
| `.agdelte-video__fullscreen` | Fullscreen button |
| `.agdelte-video__fullscreen--active` | Active modifier |
| `.agdelte-video__rate` | Rate selector group |
| `.agdelte-video__rate-btn` | Individual rate button |
| `.agdelte-video__icon` | SVG icon |
| `.agdelte-video__loading` | Loading overlay |
| `.agdelte-video__spinner` | Loading spinner |
| `.agdelte-video__error` | Error overlay |
| `.agdelte-video__error-icon` | Error icon |

## Module Structure

```
Agdelte/Html/Controls/Video/
  Types.agda          -- PlayerState, VideoModel, VideoMsg, PlayerConfig,
                         ControlLayout, KeyBinding, GestureBinding
  Player.agda         -- defaultPlayerConfig, mkUpdateVideo, mkVideoCmd,
                         videoSubs, videoPlayer (top-level widget)
  Controls.agda       -- playPauseBtn, seekBar, volumeControl, timeDisplay,
                         fullscreenBtn, rateSelector, defaultLayout,
                         controlsOverlay
  Source.agda          -- initVideoSource, MediaSource lifecycle, buffer query
  SegmentLoader.agda   -- signUrl, loadSegment (fetch pipeline)
  Util.agda            -- JS postulates: formatTime, seekPercent,
                         bufferedPercent, offsetVolume, clampVolume,
                         offsetTime, parseM3U8, jsonArrayGet, jsonArrayLength,
                         classifyGesture, gestureType, gestureMagnitude
  Properties.agda      -- Compile-time proofs: eqState reflexivity/symmetry,
                         isPlaying/isPaused consistency, toggle involution,
                         Error absorption, defaultVideoModel invariants
```

## Touch Gestures

The player supports configurable touch gestures via `pcGestures` in `PlayerConfig`.
Touch events on the player container are captured and classified by a JS postulate.

### Default Gestures

| Gesture | Action |
|---------|--------|
| Tap | Toggle play/pause |
| Double-tap left | Seek -10s |
| Double-tap right | Seek +10s |
| Horizontal swipe | Seek by displacement |
| Vertical swipe (right side) | Adjust volume |

### Gesture Dispatch

Gesture classification produces a `Cmd A` (parent message type), not `Cmd VideoMsg`.
The consumer must call `mkGestureCmd` in their cmd function:

```agda
cmdApp (VideoAction vm) m =
  mapCmd VideoAction (mkVideoCmd cfg vm (videoState m))
  <> mkGestureCmd cfg vm (videoState m)
```

Gestures can be customized or disabled via `pcGestures` in `PlayerConfig`.

## Future

- **Content protection**: The `pcSignUrl` field enables URL signing for segment
  fetches. `TokenRefreshed`, `KeyLoaded`, and `ProtectionError` message
  constructors exist for future signed-URL and encryption support.
  Client-side `decryptAES128` Task is available for segment decryption.
  The full server-side protection pipeline (token management, key rotation,
  watermarking) is planned separately.
