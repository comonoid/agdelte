{-# OPTIONS --without-K #-}

-- Shared types for the Video Player component.
-- Imported by Player, Controls, Source, SegmentLoader.

module Agdelte.Html.Controls.Video.Types where

open import Data.String using (String)
open import Data.List using (List; [])
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; not)
open import Data.Maybe using (Maybe; just; nothing)

open import Agdelte.Reactive.Node.Core using (Node; Transition; mkTransition)

------------------------------------------------------------------------
-- PlayerState
------------------------------------------------------------------------

data PlayerState : Set where
  Idle Loading Playing Paused Ended Error : PlayerState

isPlaying : PlayerState → Bool
isPlaying Playing = true
isPlaying _       = false

isPaused : PlayerState → Bool
isPaused Paused = true
isPaused _      = false

eqState : PlayerState → PlayerState → Bool
eqState Idle    Idle    = true
eqState Loading Loading = true
eqState Playing Playing = true
eqState Paused  Paused  = true
eqState Ended   Ended   = true
eqState Error   Error   = true
eqState _       _       = false

------------------------------------------------------------------------
-- VideoModel
------------------------------------------------------------------------

record VideoModel : Set where
  constructor mkVideoModel
  field
    state           : PlayerState
    currentTime     : String         -- seconds as String (from DOM)
    duration        : String         -- seconds as String (from DOM)
    volume          : String         -- [0..1] as String
    muted           : Bool
    fullscreen      : Bool
    buffered        : String         -- furthest buffered position, seconds
    playbackRate    : String         -- "1" default
    error           : Maybe String   -- last error message
    controlsVisible : Bool           -- whether controls overlay is shown
    -- Segment tracking
    currentSegment  : ℕ
    totalSegments   : ℕ
    segmentUrls     : String         -- JSON array of segment URLs
    manifestUrl     : String
    sourceReady     : Bool           -- MediaSource is open
    -- Touch tracking (for gesture detection)
    touchStartX     : String         -- start X coordinate
    touchStartY     : String         -- start Y coordinate

open VideoModel public

defaultVideoModel : VideoModel
defaultVideoModel = mkVideoModel
  Idle "0" "0" "0.8"
  false false "0" "1"
  nothing true
  0 0 "[]" "" false
  "0" "0"

------------------------------------------------------------------------
-- VideoMsg
------------------------------------------------------------------------

data VideoMsg : Set where
  -- Playback
  Play Pause TogglePlay : VideoMsg
  Seek        : String → VideoMsg       -- relative offset ("-5", "+10")
  SeekTo      : String → VideoMsg       -- absolute position ("42.5")
  SetVolume   : String → VideoMsg       -- absolute volume ("0.5")
  AdjustVolume : String → VideoMsg     -- relative volume ("+0.05", "-0.1")
  ToggleMute  : VideoMsg
  SetRate     : String → VideoMsg
  -- Fullscreen
  EnterFullscreen ExitFullscreen ToggleFullscreen : VideoMsg
  -- DOM events
  TimeUpdated       : String → VideoMsg
  DurationLoaded    : String → VideoMsg
  VolumeChanged     : String → VideoMsg
  MediaEnded        : VideoMsg
  MediaError        : String → VideoMsg
  -- Segment events
  ManifestLoaded    : String → VideoMsg
  ManifestError     : String → VideoMsg
  SourceReady       : VideoMsg
  SourceError       : String → VideoMsg
  LoadNextSegment   : VideoMsg
  SegmentFetched    : ℕ → String → VideoMsg
  SegmentAppended   : ℕ → VideoMsg
  SegmentError      : ℕ → String → VideoMsg
  AllSegmentsLoaded : VideoMsg
  BufferedUpdated   : String → VideoMsg   -- furthest buffered time
  -- UI
  ControlsShow ControlsHide : VideoMsg
  ControlsActivity  : VideoMsg
  -- Touch / gesture
  TouchStart        : String → VideoMsg   -- JSON: "x,y,time"
  TouchEnd          : String → VideoMsg   -- JSON: "x,y,time,screenWidth"
  -- Protection (future layers)
  TokenRefreshed    : String → VideoMsg
  KeyLoaded         : String → VideoMsg
  ProtectionError   : String → VideoMsg

------------------------------------------------------------------------
-- KeyBinding
------------------------------------------------------------------------

record KeyBinding (A : Set) : Set where
  constructor mkKB
  field
    kbKey   : String
    kbShift : Bool
    kbCtrl  : Bool
    kbAlt   : Bool
    kbMsg   : A

open KeyBinding public

------------------------------------------------------------------------
-- GestureBinding
------------------------------------------------------------------------

data GestureType : Set where
  Tap DoubleTapLeft DoubleTapRight : GestureType
  SwipeH SwipeVL SwipeVR Pinch    : GestureType

record GestureBinding (A : Set) : Set where
  constructor mkGesture
  field
    gbGesture : GestureType
    gbMsg     : String → A

open GestureBinding public

------------------------------------------------------------------------
-- ControlLayout
------------------------------------------------------------------------

record ControlLayout (M A : Set) : Set where
  constructor mkLayout
  field
    topLeft      : List (Node M A)
    topCenter    : List (Node M A)
    topRight     : List (Node M A)
    left         : List (Node M A)
    right        : List (Node M A)
    bottomLeft   : List (Node M A)
    bottomCenter : List (Node M A)
    bottomRight  : List (Node M A)

open ControlLayout public

emptyLayout : ∀ {M A} → ControlLayout M A
emptyLayout = mkLayout [] [] [] [] [] [] [] []

------------------------------------------------------------------------
-- PlayerConfig
------------------------------------------------------------------------

record PlayerConfig (M A : Set) : Set where
  constructor mkPlayerConfig
  field
    -- Data
    pcManifestUrl   : String
    pcAutoplay      : Bool
    pcLoop          : Bool
    pcMuted         : Bool
    pcVolume        : String
    pcPlaybackRate  : String
    -- Layout
    pcLayout        : ControlLayout M A
    pcKeymap        : List (KeyBinding A)
    pcGestures      : List (GestureBinding A)
    -- Protection
    pcSignUrl       : Maybe (String → String)
    -- Appearance
    pcContainerId   : String
    pcVideoId       : String
    -- Integration
    pcGetModel      : M → VideoModel
    pcWrapMsg       : VideoMsg → A

open PlayerConfig public

-- | Create initial VideoModel from PlayerConfig, applying config values.
initVideoModel : ∀ {M A} → PlayerConfig M A → VideoModel
initVideoModel cfg = mkVideoModel
  Idle "0" "0" (pcVolume cfg)
  (pcMuted cfg) false "0" (pcPlaybackRate cfg)
  nothing true
  0 0 "[]" (pcManifestUrl cfg) false
  "0" "0"

------------------------------------------------------------------------
-- Transitions
------------------------------------------------------------------------

controlsTransition : Transition
controlsTransition = mkTransition
  "agdelte-video__controls--visible"
  "agdelte-video__controls--hidden"
  300
