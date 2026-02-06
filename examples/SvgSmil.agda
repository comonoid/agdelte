{-# OPTIONS --without-K #-}

-- SMIL Animation Choreography Demo
-- Declarative SVG animations without JavaScript

module SvgSmil where

open import Data.List using (List; []; _∷_; [_])
open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true)

open import Agdelte.Reactive.Node
open import Agdelte.Css.Color using (hex; rgba; named)
open import Agdelte.Svg

------------------------------------------------------------------------
-- Model (minimal - animations are declarative)
------------------------------------------------------------------------

record Model : Set where
  constructor mkModel
  field
    dummy : ⊤  -- SMIL needs no model state

------------------------------------------------------------------------
-- Messages
------------------------------------------------------------------------

data Msg : Set where
  NoOp : Msg

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

updateModel : Msg → Model → Model
updateModel _ m = m

------------------------------------------------------------------------
-- View: SMIL Animation Showcase
------------------------------------------------------------------------

-- Demo 1: Choreographed sequence (fade → pulse → color) - click to replay
sequenceDemo : Node Model Msg
sequenceDemo =
  g []
    ( svgText (x_ "150" ∷ y_ "30" ∷ textAnchor_ "middle" ∷ fontSize_ "14" ∷ fill_ "#666" ∷ [])
        [ text "Click Circle to Replay Sequence" ]
    ∷ circle' (cxF 150.0 ∷ cyF 100.0 ∷ rF 30.0 ∷ fillC (hex "#4a9eff") ∷ attr "cursor" "pointer" ∷ [])
        ( -- Step 1: Fade in (starts on click)
          animate "opacity" "1" "0.3"
            (freezeEnd (withId "fadeIn" (onClick' (record defaultSmil { dur = ms 300 }))))
        ∷ animate "opacity" "0.3" "1"
            (freezeEnd (record defaultSmil
              { dur = ms 500
              ; begin' = syncEnd "fadeIn"
              }))
        ∷ -- Step 2: Pulse radius (starts after fade)
          animateValues "r" ("30" ∷ "45" ∷ "30" ∷ [])
            (withId "pulse" (record defaultSmil
              { dur = ms 600
              ; begin' = syncEnd "fadeIn"
              }))
        ∷ -- Step 3: Color shift (starts with pulse)
          animate "fill" "#4a9eff" "#ff6b6b"
            (freezeEnd (withId "colorShift" (record defaultSmil
              { dur = ms 600
              ; begin' = syncEnd "fadeIn"
              })))
        ∷ -- Step 4: Color back (after color shift)
          animate "fill" "#ff6b6b" "#4a9eff"
            (freezeEnd (record defaultSmil
              { dur = ms 400
              ; begin' = syncEnd "colorShift"
              }))
        ∷ [])
    ∷ [])

-- Demo 2: Click toggle (expand/shrink)
-- Two overlapping clickable areas that swap visibility
clickDemo : Node Model Msg
clickDemo =
  g []
    ( -- Labels
      svgText (x_ "150" ∷ y_ "180" ∷ textAnchor_ "middle" ∷ fontSize_ "14" ∷ fill_ "#666" ∷ [])
        ( text "Click to Expand"
        ∷ smilSet "visibility" "hidden"
            (freezeEnd (record defaultSmil { begin' = syncEnd "expand" }))
        ∷ smilSet "visibility" "visible"
            (freezeEnd (record defaultSmil { begin' = syncEnd "shrink" }))
        ∷ [])
    ∷ svgText (x_ "150" ∷ y_ "180" ∷ textAnchor_ "middle" ∷ fontSize_ "14" ∷ fill_ "#666" ∷ attr "visibility" "hidden" ∷ [])
        ( text "Click to Shrink"
        ∷ smilSet "visibility" "visible"
            (freezeEnd (record defaultSmil { begin' = syncEnd "expand" }))
        ∷ smilSet "visibility" "hidden"
            (freezeEnd (record defaultSmil { begin' = syncEnd "shrink" }))
        ∷ [])
    ∷ -- Visual circle (no pointer events)
      circle' (cxF 150.0 ∷ cyF 250.0 ∷ rF 25.0 ∷ fillC (hex "#10b981") ∷ attr "pointer-events" "none" ∷ [])
        ( animate "r" "25" "50"
            (freezeEnd (record defaultSmil { dur = ms 300 ; begin' = syncBegin "expand" }))
        ∷ animate "r" "50" "25"
            (freezeEnd (record defaultSmil { dur = ms 300 ; begin' = syncBegin "shrink" }))
        ∷ animate "fill" "#10b981" "#34d399"
            (freezeEnd (record defaultSmil { dur = ms 300 ; begin' = syncBegin "expand" }))
        ∷ animate "fill" "#34d399" "#10b981"
            (freezeEnd (record defaultSmil { dur = ms 300 ; begin' = syncBegin "shrink" }))
        ∷ [])
    ∷ -- Click area for EXPAND (visible initially, hidden after expand)
      circle' (cxF 150.0 ∷ cyF 250.0 ∷ rF 50.0 ∷ fill_ "transparent" ∷ attr "cursor" "pointer" ∷ [])
        ( animate "r" "0" "0"  -- dummy animation just for ID
            (withId "expand" (onClick' (record defaultSmil { dur = ms 300 })))
        ∷ smilSet "pointer-events" "none"
            (freezeEnd (record defaultSmil { begin' = syncEnd "expand" }))
        ∷ smilSet "pointer-events" "auto"
            (freezeEnd (record defaultSmil { begin' = syncEnd "shrink" }))
        ∷ [])
    ∷ -- Click area for SHRINK (hidden initially, visible after expand)
      circle' (cxF 150.0 ∷ cyF 250.0 ∷ rF 50.0 ∷ fill_ "transparent" ∷ attr "cursor" "pointer" ∷ attr "pointer-events" "none" ∷ [])
        ( animate "r" "0" "0"  -- dummy animation just for ID
            (withId "shrink" (onClick' (record defaultSmil { dur = ms 300 })))
        ∷ smilSet "pointer-events" "auto"
            (freezeEnd (record defaultSmil { begin' = syncEnd "expand" }))
        ∷ smilSet "pointer-events" "none"
            (freezeEnd (record defaultSmil { begin' = syncEnd "shrink" }))
        ∷ [])
    ∷ [])

-- Demo 3: Continuous rotation
rotationDemo : Node Model Msg
rotationDemo =
  g []
    ( svgText (x_ "400" ∷ y_ "30" ∷ textAnchor_ "middle" ∷ fontSize_ "14" ∷ fill_ "#666" ∷ [])
        [ text "Continuous Rotation" ]
    ∷ g (transform_ "translate(400, 100)" ∷ [])
        ( rect' (x_ "-25" ∷ y_ "-25" ∷ width_ "50" ∷ height_ "50" ∷ fillC (hex "#8b5cf6") ∷ rx_ "8" ∷ [])
            ( animateTransform rotateT "0" "360"
                (loop (record defaultSmil { dur = sec 3.0 }))
            ∷ [])
        ∷ [])
    ∷ [])

-- Demo 4: Hover effect
hoverDemo : Node Model Msg
hoverDemo =
  g []
    ( svgText (x_ "400" ∷ y_ "180" ∷ textAnchor_ "middle" ∷ fontSize_ "14" ∷ fill_ "#666" ∷ [])
        [ text "Hover to Scale" ]
    ∷ g (transform_ "translate(400, 250)" ∷ [])
        ( rect' (x_ "-30" ∷ y_ "-30" ∷ width_ "60" ∷ height_ "60" ∷ fillC (hex "#f59e0b") ∷ rx_ "8" ∷ attr "cursor" "pointer" ∷ [])
            ( -- Scale up on mouseover
              animateTransform scaleT "1 1" "1.3 1.3"
                (freezeEnd (record defaultSmil
                  { dur = ms 200
                  ; begin' = onEvent "mouseover"
                  }))
            ∷ -- Scale back on mouseout
              animateTransform scaleT "1.3 1.3" "1 1"
                (freezeEnd (record defaultSmil
                  { dur = ms 200
                  ; begin' = onEvent "mouseout"
                  }))
            ∷ [])
        ∷ [])
    ∷ [])

-- Demo 5: Keyframe bounce
bounceDemo : Node Model Msg
bounceDemo =
  g []
    ( svgText (x_ "150" ∷ y_ "330" ∷ textAnchor_ "middle" ∷ fontSize_ "14" ∷ fill_ "#666" ∷ [])
        [ text "Keyframe Bounce (infinite)" ]
    ∷ circle' (cxF 150.0 ∷ cyF 400.0 ∷ rF 20.0 ∷ fillC (hex "#ec4899") ∷ [])
        ( animateValues "cy" ("400" ∷ "360" ∷ "400" ∷ "380" ∷ "400" ∷ [])
            (loop (record defaultSmil { dur = ms 1000 }))
        ∷ [])
    ∷ [])

-- Demo 6: Motion along path
motionDemo : Node Model Msg
motionDemo =
  g []
    ( svgText (x_ "400" ∷ y_ "330" ∷ textAnchor_ "middle" ∷ fontSize_ "14" ∷ fill_ "#666" ∷ [])
        [ text "Motion Along Path" ]
    ∷ -- The path (visible)
      path' (d_ "M320 400 Q400 350 480 400 Q400 450 320 400"
            ∷ stroke_ "#ddd" ∷ strokeWidth_ "2" ∷ fill_ "none" ∷ []) []
    ∷ -- Moving circle
      circle' (rF 10.0 ∷ fillC (hex "#06b6d4") ∷ [])
        ( animateMotion "M320 400 Q400 350 480 400 Q400 450 320 400" true
            (loop (record defaultSmil { dur = sec 2.0 }))
        ∷ [])
    ∷ [])

-- Main template
smilTemplate : Node Model Msg
smilTemplate =
  div [ class "smil-demo" ]
    ( h1 [] [ text "SMIL Animation Choreography" ]
    ∷ p [ style "color" "#666" ]
        [ text "Declarative SVG animations - no JavaScript, browser handles timing" ]
    ∷ svg (viewBox_ "0 0 550 480" ∷ width_ "550" ∷ height_ "480"
          ∷ style "background" "#fafafa" ∷ style "border-radius" "8px" ∷ [])
        ( -- Background
          rect' (width_ "550" ∷ height_ "480" ∷ fill_ "#fafafa" ∷ []) []
        ∷ sequenceDemo
        ∷ clickDemo
        ∷ rotationDemo
        ∷ hoverDemo
        ∷ bounceDemo
        ∷ motionDemo
        ∷ [])
    ∷ [] )

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

smilApp : ReactiveApp Model Msg
smilApp = mkReactiveApp (mkModel tt) updateModel smilTemplate

app : ReactiveApp Model Msg
app = smilApp
