{-# OPTIONS --without-K #-}

-- SVG SMIL Animation Helpers
-- Declarative animations without JavaScript

module Agdelte.Svg.Smil where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Float using (Float)
open import Data.List using (List; []; _∷_; map; intersperse; foldr) renaming (_++_ to _++L_)
open import Data.Nat using (ℕ)
open import Data.Nat.Show renaming (show to showNat)
open import Data.String using (String; _++_)
open import Agdelte.Css.Show using (showFloat)
open import Agdelte.Reactive.Node using (Node; Attr; attr; elem)

------------------------------------------------------------------------
-- Duration
------------------------------------------------------------------------

data Duration : Set where
  ms    : ℕ → Duration        -- milliseconds
  sec   : Float → Duration    -- seconds
  indefinite' : Duration      -- infinite

showDuration : Duration → String
showDuration (ms n) = showNat n ++ "ms"
showDuration (sec f) = showFloat f ++ "s"
showDuration indefinite' = "indefinite"

------------------------------------------------------------------------
-- Timing
------------------------------------------------------------------------

data Timing : Set where
  offset     : Duration → Timing                    -- delay
  onEvent    : String → Timing                      -- "click", "mouseover"
  syncBegin  : String → Timing                      -- "otherId.begin"
  syncBeginD : String → Duration → Timing           -- "otherId.begin+1s"
  syncEnd    : String → Timing                      -- "otherId.end"
  syncEndD   : String → Duration → Timing           -- "otherId.end+500ms"
  syncRepeat : String → ℕ → Timing                  -- "otherId.repeat(2)"
  anyOf      : List Timing → Timing                 -- first to trigger

private
  concat : List String → String
  concat = foldr _++_ ""

{-# TERMINATING #-}
showTiming : Timing → String
showTiming (offset d) = showDuration d
showTiming (onEvent e) = e
showTiming (syncBegin id') = id' ++ ".begin"
showTiming (syncBeginD id' d) = id' ++ ".begin+" ++ showDuration d
showTiming (syncEnd id') = id' ++ ".end"
showTiming (syncEndD id' d) = id' ++ ".end+" ++ showDuration d
showTiming (syncRepeat id' n) = id' ++ ".repeat(" ++ showNat n ++ ")"
showTiming (anyOf ts) = concat (intersperse ";" (map showTiming ts))

------------------------------------------------------------------------
-- Calc mode and easing
------------------------------------------------------------------------

data CalcMode : Set where
  discrete linear paced spline : CalcMode

showCalcMode : CalcMode → String
showCalcMode discrete = "discrete"
showCalcMode linear = "linear"
showCalcMode paced = "paced"
showCalcMode spline = "spline"

-- Cubic bezier control points for spline mode
record KeySpline : Set where
  constructor mkSpline
  field
    x1 y1 x2 y2 : Float

showKeySpline : KeySpline → String
showKeySpline s = showFloat (KeySpline.x1 s) ++ " " ++
                  showFloat (KeySpline.y1 s) ++ " " ++
                  showFloat (KeySpline.x2 s) ++ " " ++
                  showFloat (KeySpline.y2 s)

-- Common easing presets
easeIn : KeySpline
easeIn = mkSpline 0.42 0.0 1.0 1.0

easeOut : KeySpline
easeOut = mkSpline 0.0 0.0 0.58 1.0

easeInOut : KeySpline
easeInOut = mkSpline 0.42 0.0 0.58 1.0

------------------------------------------------------------------------
-- Repeat and fill
------------------------------------------------------------------------

data RepeatCount : Set where
  times : ℕ → RepeatCount
  indefiniteR : RepeatCount

showRepeatCount : RepeatCount → String
showRepeatCount (times n) = showNat n
showRepeatCount indefiniteR = "indefinite"

data FillMode : Set where
  remove freeze : FillMode

showFillMode : FillMode → String
showFillMode remove = "remove"
showFillMode freeze = "freeze"

data Additive : Set where
  replace sum' : Additive

showAdditive : Additive → String
showAdditive replace = "replace"
showAdditive sum' = "sum"

data Restart : Set where
  always whenNotActive never' : Restart

showRestart : Restart → String
showRestart always = "always"
showRestart whenNotActive = "whenNotActive"
showRestart never' = "never"

------------------------------------------------------------------------
-- SMIL Animation record
------------------------------------------------------------------------

record SmilAnim : Set where
  constructor mkSmilAnim
  field
    dur         : Duration
    begin'      : Timing
    repeatCount : RepeatCount
    fill'       : FillMode
    additive    : Additive
    calcMode    : CalcMode
    restart     : Restart
    animId      : String         -- id for synchronization

open SmilAnim public

-- Default animation settings
defaultSmil : SmilAnim
defaultSmil = mkSmilAnim
  (sec 1.0)           -- 1 second
  (offset (ms 0))     -- start immediately
  (times 1)           -- play once
  remove              -- remove effect after
  replace             -- replace attribute
  linear              -- linear interpolation
  always              -- can restart anytime
  ""                  -- no id

------------------------------------------------------------------------
-- Animation elements
------------------------------------------------------------------------

-- Attribute animation: <animate attributeName="..." from="..." to="..." .../>
animate : ∀ {M Msg}
  → String           -- attributeName
  → String           -- from
  → String           -- to
  → SmilAnim
  → Node M Msg
animate attrName from' to' anim = elem "animate"
  ( attr "attributeName" attrName
  ∷ attr "from" from'
  ∷ attr "to" to'
  ∷ attr "dur" (showDuration (dur anim))
  ∷ attr "begin" (showTiming (begin' anim))
  ∷ attr "repeatCount" (showRepeatCount (repeatCount anim))
  ∷ attr "fill" (showFillMode (fill' anim))
  ∷ attr "additive" (showAdditive (additive anim))
  ∷ attr "calcMode" (showCalcMode (calcMode anim))
  ∷ attr "restart" (showRestart (restart anim))
  ∷ (if animId anim == "" then [] else attr "id" (animId anim) ∷ [])
  ) []
  where
    postulate _==_ : String → String → Bool
    {-# COMPILE JS _==_ = (a, b) => a === b #-}

-- Value animation with keyframes: values="v1;v2;v3"
animateValues : ∀ {M Msg}
  → String           -- attributeName
  → List String      -- values
  → SmilAnim
  → Node M Msg
animateValues attrName vals anim = elem "animate"
  ( attr "attributeName" attrName
  ∷ attr "values" (concat (intersperse ";" vals))
  ∷ attr "dur" (showDuration (dur anim))
  ∷ attr "begin" (showTiming (begin' anim))
  ∷ attr "repeatCount" (showRepeatCount (repeatCount anim))
  ∷ attr "fill" (showFillMode (fill' anim))
  ∷ attr "calcMode" (showCalcMode (calcMode anim))
  ∷ (if animId anim == "" then [] else attr "id" (animId anim) ∷ [])
  ) []
  where
    postulate _==_ : String → String → Bool
    {-# COMPILE JS _==_ = (a, b) => a === b #-}

-- Transform animation
data TransformType : Set where
  translateT rotateT scaleT skewXT skewYT : TransformType

showTransformType : TransformType → String
showTransformType translateT = "translate"
showTransformType rotateT = "rotate"
showTransformType scaleT = "scale"
showTransformType skewXT = "skewX"
showTransformType skewYT = "skewY"

animateTransform : ∀ {M Msg}
  → TransformType
  → String           -- from
  → String           -- to
  → SmilAnim
  → Node M Msg
animateTransform ttype from' to' anim = elem "animateTransform"
  ( attr "attributeName" "transform"
  ∷ attr "type" (showTransformType ttype)
  ∷ attr "from" from'
  ∷ attr "to" to'
  ∷ attr "dur" (showDuration (dur anim))
  ∷ attr "begin" (showTiming (begin' anim))
  ∷ attr "repeatCount" (showRepeatCount (repeatCount anim))
  ∷ attr "fill" (showFillMode (fill' anim))
  ∷ attr "additive" (showAdditive (additive anim))
  ∷ (if animId anim == "" then [] else attr "id" (animId anim) ∷ [])
  ) []
  where
    postulate _==_ : String → String → Bool
    {-# COMPILE JS _==_ = (a, b) => a === b #-}

-- Motion along path
animateMotion : ∀ {M Msg}
  → String           -- path data (d attribute format)
  → Bool             -- auto-rotate
  → SmilAnim
  → Node M Msg
animateMotion pathData autoRotate anim = elem "animateMotion"
  ( attr "path" pathData
  ∷ attr "dur" (showDuration (dur anim))
  ∷ attr "begin" (showTiming (begin' anim))
  ∷ attr "repeatCount" (showRepeatCount (repeatCount anim))
  ∷ attr "fill" (showFillMode (fill' anim))
  ∷ (if autoRotate then attr "rotate" "auto" ∷ [] else [])
  ++L (if animId anim == "" then [] else attr "id" (animId anim) ∷ [])
  ) []
  where
    postulate _==_ : String → String → Bool
    {-# COMPILE JS _==_ = (a, b) => a === b #-}

-- Set (discrete state change)
smilSet : ∀ {M Msg}
  → String           -- attributeName
  → String           -- to
  → SmilAnim
  → Node M Msg
smilSet attrName to' anim = elem "set"
  ( attr "attributeName" attrName
  ∷ attr "to" to'
  ∷ attr "begin" (showTiming (begin' anim))
  ∷ attr "dur" (showDuration (dur anim))
  ∷ attr "fill" (showFillMode (fill' anim))
  ∷ (if animId anim == "" then [] else attr "id" (animId anim) ∷ [])
  ) []
  where
    postulate _==_ : String → String → Bool
    {-# COMPILE JS _==_ = (a, b) => a === b #-}

------------------------------------------------------------------------
-- Choreography helpers
------------------------------------------------------------------------

-- Create animation that starts after another ends
after : String → SmilAnim → SmilAnim
after prevId anim = record anim { begin' = syncEnd prevId }

-- Create animation that starts with another
withAnim : String → SmilAnim → SmilAnim
withAnim otherId anim = record anim { begin' = syncBegin otherId }

-- Create animation that starts on click
onClick' : SmilAnim → SmilAnim
onClick' anim = record anim { begin' = onEvent "click" }

-- Infinite loop
loop : SmilAnim → SmilAnim
loop anim = record anim { repeatCount = indefiniteR }

-- Freeze at end
freezeEnd : SmilAnim → SmilAnim
freezeEnd anim = record anim { fill' = freeze }

-- Named animation (for synchronization)
withId : String → SmilAnim → SmilAnim
withId id' anim = record anim { animId = id' }
