{-# OPTIONS --without-K #-}

-- Video Player UI Controls: play/pause, seek bar, volume, time, fullscreen, rate.
-- Each widget is parametric in (M A : Set) with getter/wrapper for zoom composition.
-- CSS classes: .agdelte-video__*  (BEM convention)

module Agdelte.Html.Controls.Video.Controls where

open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_)

open import Agdelte.Reactive.Node
open import Agdelte.Html.Controls.Util using (eqStr)
open import Agdelte.Html.Controls.Video.Types
open import Agdelte.Html.Controls.Video.Util

------------------------------------------------------------------------
-- SVG Icons (inline, minimal)
------------------------------------------------------------------------

private
  playIcon : ∀ {M A} → Node M A
  playIcon = elem "svg"
    ( attr "viewBox" "0 0 24 24"
    ∷ class "agdelte-video__icon"
    ∷ [] )
    ( elem "polygon" ( attr "points" "5,3 19,12 5,21" ∷ [] ) [] ∷ [] )

  pauseIcon : ∀ {M A} → Node M A
  pauseIcon = elem "svg"
    ( attr "viewBox" "0 0 24 24"
    ∷ class "agdelte-video__icon"
    ∷ [] )
    ( elem "rect" ( attr "x" "5" ∷ attr "y" "3" ∷ attr "width" "4" ∷ attr "height" "18" ∷ [] ) []
    ∷ elem "rect" ( attr "x" "15" ∷ attr "y" "3" ∷ attr "width" "4" ∷ attr "height" "18" ∷ [] ) []
    ∷ [] )

  volumeIcon : ∀ {M A} → Node M A
  volumeIcon = elem "svg"
    ( attr "viewBox" "0 0 24 24"
    ∷ class "agdelte-video__icon"
    ∷ [] )
    ( elem "polygon" ( attr "points" "11,5 6,9 2,9 2,15 6,15 11,19" ∷ [] ) []
    ∷ elem "path" ( attr "d" "M15.54 8.46a5 5 0 010 7.07" ∷ attr "fill" "none" ∷ attr "stroke" "currentColor" ∷ attr "stroke-width" "2" ∷ [] ) []
    ∷ [] )

  volumeMutedIcon : ∀ {M A} → Node M A
  volumeMutedIcon = elem "svg"
    ( attr "viewBox" "0 0 24 24"
    ∷ class "agdelte-video__icon"
    ∷ [] )
    ( elem "polygon" ( attr "points" "11,5 6,9 2,9 2,15 6,15 11,19" ∷ [] ) []
    ∷ elem "line" ( attr "x1" "23" ∷ attr "y1" "9" ∷ attr "x2" "17" ∷ attr "y2" "15" ∷ attr "stroke" "currentColor" ∷ attr "stroke-width" "2" ∷ [] ) []
    ∷ elem "line" ( attr "x1" "17" ∷ attr "y1" "9" ∷ attr "x2" "23" ∷ attr "y2" "15" ∷ attr "stroke" "currentColor" ∷ attr "stroke-width" "2" ∷ [] ) []
    ∷ [] )

  fullscreenIcon : ∀ {M A} → Node M A
  fullscreenIcon = elem "svg"
    ( attr "viewBox" "0 0 24 24"
    ∷ class "agdelte-video__icon"
    ∷ [] )
    ( elem "path" ( attr "d" "M8 3H5a2 2 0 00-2 2v3m18 0V5a2 2 0 00-2-2h-3m0 18h3a2 2 0 002-2v-3M3 16v3a2 2 0 002 2h3" ∷ attr "fill" "none" ∷ attr "stroke" "currentColor" ∷ attr "stroke-width" "2" ∷ [] ) []
    ∷ [] )

------------------------------------------------------------------------
-- Play / Pause button
------------------------------------------------------------------------

playPauseBtn : ∀ {M A} → (M → VideoModel) → (VideoMsg → A) → Node M A
playPauseBtn get wrap =
  button
    ( classBind (λ m →
        if isPlaying (state (get m))
        then "agdelte-video__play-pause agdelte-video__play-pause--playing"
        else "agdelte-video__play-pause agdelte-video__play-pause--paused")
    ∷ onClick (wrap TogglePlay)
    ∷ [] )
    ( when (λ m → isPlaying (state (get m))) pauseIcon
    ∷ when (λ m → not (isPlaying (state (get m)))) playIcon
    ∷ [] )

------------------------------------------------------------------------
-- Seek bar
------------------------------------------------------------------------

seekBar : ∀ {M A} → (M → VideoModel) → (VideoMsg → A) → Node M A
seekBar get wrap =
  div ( class "agdelte-video__seek" ∷ [] )
    ( -- Buffered progress (background bar)
      div ( class "agdelte-video__seek-buffered"
          ∷ styleBind "width" (mkBinding
              (λ m → bufferedPercent (buffered (get m)) (duration (get m)) ++ "%")
              eqStr)
          ∷ [] ) []
    ∷ -- Played progress (foreground bar)
      div ( class "agdelte-video__seek-played"
          ∷ styleBind "width" (mkBinding
              (λ m → seekPercent (currentTime (get m)) (duration (get m)) ++ "%")
              eqStr)
          ∷ [] ) []
    ∷ -- Input range for interaction
      input ( type' "range"
            ∷ class "agdelte-video__seek-input"
            ∷ attr "min" "0"
            ∷ attrBind "max" (stringBinding (λ m → duration (get m)))
            ∷ attr "step" "0.1"
            ∷ valueBind (λ m → currentTime (get m))
            ∷ onInput (wrap ∘ SeekTo)
            ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Volume control
------------------------------------------------------------------------

volumeControl : ∀ {M A} → (M → VideoModel) → (VideoMsg → A) → Node M A
volumeControl get wrap =
  div ( class "agdelte-video__volume" ∷ [] )
    ( -- Mute button
      button
        ( classBind (λ m →
            if muted (get m)
            then "agdelte-video__volume-icon agdelte-video__volume-icon--muted"
            else "agdelte-video__volume-icon")
        ∷ onClick (wrap ToggleMute)
        ∷ [] )
        ( when (λ m → muted (get m)) volumeMutedIcon
        ∷ when (λ m → not (muted (get m))) volumeIcon
        ∷ [] )
    ∷ -- Volume slider
      input ( type' "range"
            ∷ class "agdelte-video__volume-slider"
            ∷ attr "min" "0"
            ∷ attr "max" "1"
            ∷ attr "step" "0.05"
            ∷ valueBind (λ m → volume (get m))
            ∷ onInput (wrap ∘ SetVolume)
            ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Time display
------------------------------------------------------------------------

timeDisplay : ∀ {M A} → (M → VideoModel) → (VideoMsg → A) → Node M A
timeDisplay get _ =
  span ( class "agdelte-video__time" ∷ [] )
    ( bindF (λ m → formatTime (currentTime (get m)))
    ∷ text " / "
    ∷ bindF (λ m → formatTime (duration (get m)))
    ∷ [] )

------------------------------------------------------------------------
-- Fullscreen button
------------------------------------------------------------------------

fullscreenBtn : ∀ {M A} → (M → VideoModel) → (VideoMsg → A) → Node M A
fullscreenBtn get wrap =
  button
    ( classBind (λ m →
        if fullscreen (get m)
        then "agdelte-video__fullscreen agdelte-video__fullscreen--active"
        else "agdelte-video__fullscreen")
    ∷ onClick (wrap ToggleFullscreen)
    ∷ [] )
    ( fullscreenIcon ∷ [] )

------------------------------------------------------------------------
-- Playback rate selector
------------------------------------------------------------------------

rateSelector : ∀ {M A} → (M → VideoModel) → (VideoMsg → A) → Node M A
rateSelector get wrap =
  div ( class "agdelte-video__rate" ∷ [] )
    ( button ( class "agdelte-video__rate-btn" ∷ onClick (wrap (SetRate "0.5")) ∷ [] )
        ( text "0.5x" ∷ [] )
    ∷ button ( class "agdelte-video__rate-btn" ∷ onClick (wrap (SetRate "1")) ∷ [] )
        ( text "1x" ∷ [] )
    ∷ button ( class "agdelte-video__rate-btn" ∷ onClick (wrap (SetRate "1.5")) ∷ [] )
        ( text "1.5x" ∷ [] )
    ∷ button ( class "agdelte-video__rate-btn" ∷ onClick (wrap (SetRate "2")) ∷ [] )
        ( text "2x" ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Default layout
------------------------------------------------------------------------

defaultLayout : ∀ {M A} → (M → VideoModel) → (VideoMsg → A) → ControlLayout M A
defaultLayout get wrap = mkLayout
  [] [] [] [] []
  ( playPauseBtn get wrap ∷ volumeControl get wrap ∷ timeDisplay get wrap ∷ [] )
  ( seekBar get wrap ∷ [] )
  ( rateSelector get wrap ∷ fullscreenBtn get wrap ∷ [] )

------------------------------------------------------------------------
-- Controls overlay
------------------------------------------------------------------------

controlsOverlay : ∀ {M A} → PlayerConfig M A → Node M A
controlsOverlay cfg =
  let get    = pcGetModel cfg
      layout = pcLayout cfg
  in
  whenT (λ m → controlsVisible (get m)) controlsTransition
    (div ( class "agdelte-video__controls"
         ∷ onMouseMove (λ _ → pcWrapMsg cfg ControlsActivity)
         ∷ [] )
      ( div ( class "agdelte-video__controls-top" ∷ [] )
          ( div ( class "agdelte-video__slot--top-left" ∷ [] ) (topLeft layout)
          ∷ div ( class "agdelte-video__slot--top-center" ∷ [] ) (topCenter layout)
          ∷ div ( class "agdelte-video__slot--top-right" ∷ [] ) (topRight layout)
          ∷ [] )
      ∷ div ( class "agdelte-video__controls-middle" ∷ [] )
          ( div ( class "agdelte-video__slot--left" ∷ [] ) (left layout)
          ∷ div ( class "agdelte-video__slot--right" ∷ [] ) (right layout)
          ∷ [] )
      ∷ div ( class "agdelte-video__controls-bottom" ∷ [] )
          ( div ( class "agdelte-video__slot--bottom-left" ∷ [] ) (bottomLeft layout)
          ∷ div ( class "agdelte-video__slot--bottom-center" ∷ [] ) (bottomCenter layout)
          ∷ div ( class "agdelte-video__slot--bottom-right" ∷ [] ) (bottomRight layout)
          ∷ [] )
      ∷ [] ))
