{-# OPTIONS --without-K #-}

-- Video Player: state machine, update/cmd, top-level widget, subscriptions.
-- Public API for the video player component.

module Agdelte.Html.Controls.Video.Player where

open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_)
open import Data.Bool using (Bool; true; false; not; if_then_else_; _∧_)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Function using (_∘_)

open import Agdelte.Core.Cmd as Cmd using
  ( Cmd; ε; _<>_
  ; callMethod; setProp; delay
  ; attempt
  ; mediaSourceInit; mediaSourceAppend; mediaSourceEnd
  ; mapCmd
  )
open import Agdelte.Core.Task as Task using (Task; Result; ok; err)
open import Agdelte.Core.Event as Event using (Event; never; timeout; mapE)

open import Agdelte.Reactive.Node
open import Agdelte.Html.Controls.Util using (eqStr)
open import Agdelte.Html.Controls.Video.Types public
open import Agdelte.Html.Controls.Video.Util
  using ( formatTime; formatTimeLong; seekPercent; bufferedPercent
        ; offsetVolume; clampVolume; offsetTime
        ; parseM3U8; jsonArrayGet; jsonArrayLength
        ; classifyGesture; gestureType; gestureMagnitude
        ; parseTouchX; parseTouchY; parseTouchScreenW )
open import Agdelte.Html.Controls.Video.Controls
  using ( playPauseBtn; seekBar; volumeControl; timeDisplay
        ; fullscreenBtn; rateSelector; defaultLayout; controlsOverlay )
open import Agdelte.Html.Controls.Video.Source using (initVideoSource)
open import Agdelte.Html.Controls.Video.SegmentLoader using (loadSegment)

------------------------------------------------------------------------
-- Default keymap
------------------------------------------------------------------------

-- | Composite key format: "S-C-A-key" encodes shift/ctrl/alt modifiers.
-- Runtime builds composite from KeyboardEvent and matches against these.
defaultKeymap : ∀ {A} → (VideoMsg → A) → List (KeyBinding A)
defaultKeymap wrap =
    mkKB " "               false false false (wrap TogglePlay)
  ∷ mkKB "ArrowLeft"       false false false (wrap (Seek "-5"))
  ∷ mkKB "ArrowRight"      false false false (wrap (Seek "+5"))
  ∷ mkKB "S-ArrowLeft"     true  false false (wrap (Seek "-10"))
  ∷ mkKB "S-ArrowRight"    true  false false (wrap (Seek "+10"))
  ∷ mkKB "m"               false false false (wrap ToggleMute)
  ∷ mkKB "f"               false false false (wrap ToggleFullscreen)
  ∷ mkKB "ArrowUp"         false false false (wrap (AdjustVolume "+0.05"))
  ∷ mkKB "ArrowDown"       false false false (wrap (AdjustVolume "-0.05"))
  ∷ mkKB "Escape"          false false false (wrap ExitFullscreen)
  ∷ []

------------------------------------------------------------------------
-- Default config
------------------------------------------------------------------------

-- | Default gesture bindings: tap → toggle play,
-- swipe horizontal → seek, swipe vertical right → volume.
-- Double-tap detection requires stateful tracking and is not yet implemented.
defaultGestures : ∀ {A} → (VideoMsg → A) → List (GestureBinding A)
defaultGestures wrap =
    mkGesture Tap            (λ _ → wrap TogglePlay)
  ∷ mkGesture SwipeH         (λ mag → wrap (Seek mag))
  ∷ mkGesture SwipeVR        (λ mag → wrap (AdjustVolume mag))
  ∷ []

defaultPlayerConfig : ∀ {M A}
  → String                   -- manifest URL
  → (M → VideoModel)         -- getter
  → (VideoMsg → A)           -- wrapper
  → PlayerConfig M A
defaultPlayerConfig url get wrap = mkPlayerConfig
  url false false false "0.8" "1"
  (defaultLayout get wrap)
  (defaultKeymap wrap)
  (defaultGestures wrap)
  nothing
  "agdelte-video-container"
  "agdelte-video"
  get wrap

------------------------------------------------------------------------
-- Gesture dispatch
------------------------------------------------------------------------

private
  -- | Match gesture type string against GestureBinding list, dispatch msg
  dispatchGesture : ∀ {A} → List (GestureBinding A) → String → String → Maybe A
  dispatchGesture [] _ _ = nothing
  dispatchGesture (g ∷ gs) gtype mag =
    if matchGType (gbGesture g) gtype
    then just (gbMsg g mag)
    else dispatchGesture gs gtype mag
    where
    matchGType : GestureType → String → Bool
    matchGType Tap            s = eqStr s "tap"
    matchGType DoubleTapLeft  s = eqStr s "double-tap-left"
    matchGType DoubleTapRight s = eqStr s "double-tap-right"
    matchGType SwipeH         s = eqStr s "swipe-h"
    matchGType SwipeVL        s = eqStr s "swipe-vl"
    matchGType SwipeVR        s = eqStr s "swipe-vr"
    matchGType Pinch          s = eqStr s "pinch"

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

mkUpdateVideo : ∀ {M A} → PlayerConfig M A → VideoMsg → VideoModel → VideoModel
mkUpdateVideo cfg = go
  where
  go : VideoMsg → VideoModel → VideoModel
  go Play m             = if eqState (state m) Error then m
                          else record m { state = Playing ; controlsVisible = true }
  go Pause m            = if eqState (state m) Error then m
                          else record m { state = Paused ; controlsVisible = true }
  go TogglePlay m       = if eqState (state m) Error then m
                          else record m { state = if isPlaying (state m) then Paused else Playing }
  go (Seek _) m         = m
  go (SeekTo _) m       = m
  go (SetVolume v) m    = record m { volume = clampVolume v }
  go (AdjustVolume d) m = record m { volume = offsetVolume (volume m) d }
  go ToggleMute m       = record m { muted = not (muted m) }
  go (SetRate r) m      = record m { playbackRate = r }
  go EnterFullscreen m  = record m { fullscreen = true }
  go ExitFullscreen m   = record m { fullscreen = false }
  go ToggleFullscreen m = record m { fullscreen = not (fullscreen m) }
  go (TimeUpdated t) m  = record m { currentTime = t }
  go (DurationLoaded d) m = record m { duration = d
                                      ; state = if pcAutoplay cfg then Playing else Paused }
  go (VolumeChanged v) m  = record m { volume = v }
  go MediaEnded m         = record m { state = if pcLoop cfg then Playing else Ended }
  go (MediaError e) m     = record m { state = Error ; error = just e }
  go (ManifestLoaded raw) m =
    let urls  = parseM3U8 raw
        count = jsonArrayLength urls
    in if zero <ᵇ count
       then record m { segmentUrls = urls ; totalSegments = count ; state = Loading }
       else record m { state = Error ; error = just "Empty manifest: no segments found" }
  go (ManifestError e) m  = record m { state = Error ; error = just e }
  go SourceReady m        = record m { sourceReady = true }
  go (SourceError e) m    = record m { state = Error ; error = just e }
  go LoadNextSegment m    = m
  go (SegmentFetched _ _) m = m
  go (SegmentAppended n) m  = record m { currentSegment = suc n }
  go AllSegmentsLoaded m    = m
  go (BufferedUpdated b) m  = record m { buffered = b }
  go (SegmentError _ e) m   = record m { state = Error ; error = just e }
  go ControlsShow m       = record m { controlsVisible = true }
  go ControlsHide m       = record m { controlsVisible = false }
  go ControlsActivity m   = record m { controlsVisible = true }
  go (TouchStart s) m     = record m { touchStartX = parseTouchX s
                                      ; touchStartY = parseTouchY s }
  go (TouchEnd _) m       = m   -- gesture dispatch happens in cmd
  go (TokenRefreshed _) m = m
  go (KeyLoaded _) m      = m
  go (ProtectionError e) m = record m { state = Error ; error = just e }

------------------------------------------------------------------------
-- Segment loading command helper
------------------------------------------------------------------------

loadSegmentCmd : ∀ {M A} → PlayerConfig M A → VideoModel → ℕ → Cmd VideoMsg
loadSegmentCmd cfg m idx =
  let url = jsonArrayGet (segmentUrls m) idx
  in attempt (loadSegment cfg url)
       (λ { (ok dat)  → SegmentFetched idx dat
          ; (err msg) → SegmentError idx msg })

------------------------------------------------------------------------
-- Cmd
------------------------------------------------------------------------

mkVideoCmd : ∀ {M A} → PlayerConfig M A → VideoMsg → VideoModel → Cmd VideoMsg
mkVideoCmd cfg = go
  where
  vid = "#" ++ pcVideoId cfg
  cid = "#" ++ pcContainerId cfg
  go : VideoMsg → VideoModel → Cmd VideoMsg
  -- Playback
  go Play _                 = callMethod vid "play"
  go Pause _                = callMethod vid "pause"
  go TogglePlay m           = if isPlaying (state m)
                              then callMethod vid "pause"
                              else callMethod vid "play"
  go (Seek t) m             = setProp vid "currentTime"
                                (offsetTime (currentTime m) t (duration m))
  go (SeekTo t) _           = setProp vid "currentTime" t
  go (SetVolume v) _        = setProp vid "volume" (clampVolume v)
  go (AdjustVolume d) m     = setProp vid "volume" (offsetVolume (volume m) d)
  go ToggleMute m           = setProp vid "muted"
                                (if muted m then "false" else "true")
  go (SetRate r) _          = setProp vid "playbackRate" r
  go ToggleFullscreen _     = callMethod cid "requestFullscreen"
  go EnterFullscreen _      = callMethod cid "requestFullscreen"
  go ExitFullscreen _       = callMethod "document" "exitFullscreen"

  -- Source lifecycle
  go (DurationLoaded _) _   = if pcAutoplay cfg then callMethod vid "play" else ε
  go (ManifestLoaded _) m   =
    -- Manifest parsed in update; now init MediaSource if not already ready
    if sourceReady m then ε
    else mediaSourceInit vid "video/mp4; codecs=\"avc1.42E01E, mp4a.40.2\""
           SourceReady SourceError
  go SourceReady m           =
    if zero <ᵇ totalSegments m then loadSegmentCmd cfg m 0 else ε
  go (SegmentFetched n base64data) _ =
    mediaSourceAppend vid base64data (SegmentAppended n) (λ e → SegmentError n e)
  go (SegmentAppended n) m  =
    let next = suc n
    in if next <ᵇ totalSegments m then loadSegmentCmd cfg m next
       else mediaSourceEnd vid
  go LoadNextSegment m      = loadSegmentCmd cfg m (currentSegment m)

  -- Loop
  go MediaEnded m           = if pcLoop cfg
                              then callMethod vid "play" <> setProp vid "currentTime" "0"
                              else ε
  -- Default
  go _ _                    = ε

------------------------------------------------------------------------
-- Gesture command (returns Cmd A, not Cmd VideoMsg)
------------------------------------------------------------------------

-- | Classify a touch gesture and dispatch the bound action.
-- Called by the consumer's cmd function on TouchEnd:
--   cmdApp (VideoAction (TouchEnd s)) m =
--     mkGestureCmd appVideoConfig (TouchEnd s) (videoState m)
private
  maybeFire : ∀ {A} → Maybe A → Cmd A
  maybeFire nothing  = ε
  maybeFire (just a) = delay 0 a

mkGestureCmd : ∀ {M A} → PlayerConfig M A → VideoMsg → VideoModel → Cmd A
mkGestureCmd cfg (TouchEnd s) m =
  let endX = parseTouchX s
      endY = parseTouchY s
      screenW = parseTouchScreenW s
      result = classifyGesture (touchStartX m) (touchStartY m) endX endY
                 screenW
      gtype = gestureType result
      mag   = gestureMagnitude result
  in maybeFire (dispatchGesture (pcGestures cfg) gtype mag)
mkGestureCmd _ _ _ = ε

------------------------------------------------------------------------
-- Subscriptions
------------------------------------------------------------------------

videoSubs : VideoModel → Event VideoMsg
videoSubs m =
  -- Auto-hide controls after 3s of inactivity (when playing and visible)
  if isPlaying (state m) ∧ controlsVisible m
  then timeout 3000 ControlsHide
  else never

------------------------------------------------------------------------
-- Keyboard handling
------------------------------------------------------------------------

private
  keymapKeys : ∀ {M A} → PlayerConfig M A → List String
  keymapKeys cfg = go (pcKeymap cfg)
    where
    go : ∀ {X} → List (KeyBinding X) → List String
    go [] = []
    go (kb ∷ kbs) = kbKey kb ∷ go kbs

  handleKeypress : ∀ {M A} → PlayerConfig M A → String → A
  handleKeypress {_} {A} cfg k = go (pcKeymap cfg)
    where
    go : List (KeyBinding A) → A
    go [] = pcWrapMsg cfg ControlsActivity
    go (kb ∷ kbs) = if eqStr k (kbKey kb) then kbMsg kb else go kbs

------------------------------------------------------------------------
-- Top-level widget
------------------------------------------------------------------------

private
  -- Loading overlay: shown when state = Loading
  loadingOverlay : ∀ {M A} → (M → VideoModel) → Node M A
  loadingOverlay get =
    when (λ m → eqState (state (get m)) Loading)
      (div ( class "agdelte-video__loading" ∷ [] )
        ( div ( class "agdelte-video__spinner" ∷ [] ) []
        ∷ [] ))

  -- Error overlay: shown when state = Error
  errorOverlay : ∀ {M A} → (M → VideoModel) → Node M A
  errorOverlay get =
    when (λ m → eqState (state (get m)) Error)
      (div ( class "agdelte-video__error" ∷ [] )
        ( div ( class "agdelte-video__error-icon" ∷ [] )
            ( text "!" ∷ [] )
        ∷ bindF (λ m → fromMaybe "Playback error" (error (get m)))
        ∷ [] ))

videoPlayer : ∀ {M A} → PlayerConfig M A → Node M A
videoPlayer cfg =
  let get = pcGetModel cfg
  in
  div ( class "agdelte-video"
      ∷ id' (pcContainerId cfg)
      ∷ attr "tabindex" "0"
      ∷ onKeyFiltered (keymapKeys cfg) (handleKeypress cfg)
      ∷ onValueFrom "touchstart" "touch.start" (pcWrapMsg cfg ∘ TouchStart)
      ∷ onValueFrom "touchend" "touch.end" (pcWrapMsg cfg ∘ TouchEnd)
      ∷ [] )
    ( -- The <video> element (headless — no browser controls)
      video
        ( id' (pcVideoId cfg)
        ∷ class "agdelte-video__media"
        ∷ attr "playsinline" "true"
        ∷ onTimeUpdate (pcWrapMsg cfg ∘ TimeUpdated)
        ∷ onLoadedMetadata (pcWrapMsg cfg ∘ DurationLoaded)
        ∷ onVolumeChange (pcWrapMsg cfg ∘ VolumeChanged)
        ∷ onEnded (pcWrapMsg cfg MediaEnded)
        ∷ onProgress (pcWrapMsg cfg ∘ BufferedUpdated)
        ∷ on "play" (pcWrapMsg cfg Play)
        ∷ on "pause" (pcWrapMsg cfg Pause)
        ∷ [] )
        []
    ∷ -- Loading spinner
      loadingOverlay get
    ∷ -- Error display
      errorOverlay get
    ∷ -- Controls overlay
      controlsOverlay cfg
    ∷ [] )
