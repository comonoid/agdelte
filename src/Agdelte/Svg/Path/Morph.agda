{-# OPTIONS --without-K #-}

-- Path Morphing and Line-Drawing Animation
-- Interpolation between paths and stroke-dasharray animation

module Agdelte.Svg.Path.Morph where

open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.List using (List; []; _∷_; zipWith; map; length)
open import Data.Nat using (ℕ)
open import Data.String using (String; _++_)
open import Data.Bool using (Bool)
open import Agdelte.Css.Show using (showFloat)
open import Agdelte.Reactive.Node using (Attr; attr; attrBind; Binding; stringBinding)
open import Agdelte.Svg.Path

------------------------------------------------------------------------
-- Linear interpolation
------------------------------------------------------------------------

-- Lerp for Float
lerpFloat : Float → Float → Float → Float
lerpFloat a b t = a + (b - a) * t

-- Lerp for Point
lerpPoint : Point → Point → Float → Point
lerpPoint a b t = (lerpFloat (x a) (x b) t) , (lerpFloat (y a) (y b) t)

-- Lerp for Bool (snap at 0.5)
lerpBool : Bool → Bool → Float → Bool
lerpBool a b t with t
... | _ = if t < 0.5 then a else b
  where
    postulate _<_ : Float → Float → Bool
    {-# COMPILE JS _<_ = (a, b) => a < b #-}
    open import Data.Bool using (if_then_else_)

------------------------------------------------------------------------
-- Path command interpolation
------------------------------------------------------------------------

-- Interpolate between two compatible path commands
-- Commands must have same type (M-M, L-L, etc.)
lerpCmd : PathCmd → PathCmd → Float → PathCmd
lerpCmd (M a) (M b) t = M (lerpPoint a b t)
lerpCmd (L a) (L b) t = L (lerpPoint a b t)
lerpCmd (H a) (H b) t = H (lerpFloat a b t)
lerpCmd (V a) (V b) t = V (lerpFloat a b t)
lerpCmd (C a1 a2 a3) (C b1 b2 b3) t = C (lerpPoint a1 b1 t) (lerpPoint a2 b2 t) (lerpPoint a3 b3 t)
lerpCmd (S a1 a2) (S b1 b2) t = S (lerpPoint a1 b1 t) (lerpPoint a2 b2 t)
lerpCmd (Q a1 a2) (Q b1 b2) t = Q (lerpPoint a1 b1 t) (lerpPoint a2 b2 t)
lerpCmd (T a) (T b) t = T (lerpPoint a b t)
lerpCmd (A arx ary arot alrg asw ap) (A brx bry brot blrg bsw bp) t =
  A (lerpFloat arx brx t)
    (lerpFloat ary bry t)
    (lerpFloat arot brot t)
    (lerpBool alrg blrg t)
    (lerpBool asw bsw t)
    (lerpPoint ap bp t)
lerpCmd Z Z t = Z
-- Relative commands
lerpCmd (mRel a) (mRel b) t = mRel (lerpPoint a b t)
lerpCmd (lRel a) (lRel b) t = lRel (lerpPoint a b t)
lerpCmd (hRel a) (hRel b) t = hRel (lerpFloat a b t)
lerpCmd (vRel a) (vRel b) t = vRel (lerpFloat a b t)
lerpCmd (cRel a1 a2 a3) (cRel b1 b2 b3) t = cRel (lerpPoint a1 b1 t) (lerpPoint a2 b2 t) (lerpPoint a3 b3 t)
lerpCmd (sRel a1 a2) (sRel b1 b2) t = sRel (lerpPoint a1 b1 t) (lerpPoint a2 b2 t)
lerpCmd (qRel a1 a2) (qRel b1 b2) t = qRel (lerpPoint a1 b1 t) (lerpPoint a2 b2 t)
lerpCmd (tRel a) (tRel b) t = tRel (lerpPoint a b t)
lerpCmd (aRel arx ary arot alrg asw ap) (aRel brx bry brot blrg bsw bp) t =
  aRel (lerpFloat arx brx t)
       (lerpFloat ary bry t)
       (lerpFloat arot brot t)
       (lerpBool alrg blrg t)
       (lerpBool asw bsw t)
       (lerpPoint ap bp t)
-- Incompatible commands: return first
lerpCmd a _ _ = a

-- Interpolate between two paths (must have same structure)
lerpPath : Path → Path → Float → Path
lerpPath as bs t = zipWith (λ a b → lerpCmd a b t) as bs

------------------------------------------------------------------------
-- Line-drawing animation (stroke-dasharray)
------------------------------------------------------------------------

-- For line-drawing, we use:
--   stroke-dasharray: <length> <length>
--   stroke-dashoffset: <length>
-- At t=0: dashoffset = length (nothing visible)
-- At t=1: dashoffset = 0 (fully drawn)

-- Generate stroke-dasharray for drawing animation
-- Takes total path length
drawDasharray : Float → String
drawDasharray len = showFloat len ++ " " ++ showFloat len

-- Generate stroke-dashoffset for progress t (0 to 1)
drawDashoffset : Float → Float → String
drawDashoffset len t = showFloat (len * (1.0 - t))

-- Attribute helpers for line-drawing animation
drawStrokeDasharray : ∀ {M Msg} → Float → Attr M Msg
drawStrokeDasharray len = attr "stroke-dasharray" (drawDasharray len)

-- Dynamic stroke-dashoffset bound to model
-- Usage: drawStrokeDashoffsetBind pathLen (λ m → progress m)
drawStrokeDashoffsetBind : ∀ {M Msg} → Float → (M → Float) → Attr M Msg
drawStrokeDashoffsetBind len getProgress =
  attrBind "stroke-dashoffset" (stringBinding (λ m → drawDashoffset len (getProgress m)))

------------------------------------------------------------------------
-- Higher-level animation helpers
------------------------------------------------------------------------

-- Draw path animation state
record DrawState : Set where
  constructor mkDrawState
  field
    progress : Float  -- 0.0 to 1.0
    pathLen  : Float  -- total length

-- Attributes for drawing animation (use together)
drawPathAttrs : ∀ {M Msg} → (M → DrawState) → List (Attr M Msg)
drawPathAttrs getState =
  attrBind "stroke-dasharray" (stringBinding (λ m → drawDasharray (DrawState.pathLen (getState m))))
  ∷ attrBind "stroke-dashoffset" (stringBinding (λ m →
      let s = getState m in drawDashoffset (DrawState.pathLen s) (DrawState.progress s)))
  ∷ []
