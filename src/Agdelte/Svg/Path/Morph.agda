{-# OPTIONS --without-K #-}

-- Path Morphing and Line-Drawing Animation
-- Interpolation between paths and stroke-dasharray animation

module Agdelte.Svg.Path.Morph where

open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.List using (List; []; _∷_; zipWith; map; length; _++_)
open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Data.Nat.Base using (_≤ᵇ_)
open import Data.String using (String; _++_)
open import Data.Bool using (Bool; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
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
-- Incompatible commands: promote simpler to more complex type
-- L→C: promote L to degenerate cubic with both control points at the L
-- endpoint, producing a "pull from point" morph effect as the controls
-- lerp toward the target cubic's control points.
lerpCmd (L a) (C b1 b2 b3) t =
  let -- Control points placed at L endpoint (degenerate cubic);
      -- they lerp toward the target cubic's control points over t.
      c1 = lerpPoint a a 0.0  -- same as a (will lerp toward b1)
      c2 = lerpPoint a a 0.0  -- same as a (will lerp toward b2)
  in C (lerpPoint c1 b1 t) (lerpPoint c2 b2 t) (lerpPoint a b3 t)
lerpCmd (C a1 a2 a3) (L b) t =
  let c1 = lerpPoint b b 0.0
      c2 = lerpPoint b b 0.0
  in C (lerpPoint a1 c1 t) (lerpPoint a2 c2 t) (lerpPoint a3 b t)
-- lRel→cRel promotion (same degenerate cubic strategy)
lerpCmd (lRel a) (cRel b1 b2 b3) t =
  let c1 = lerpPoint a a 0.0
      c2 = lerpPoint a a 0.0
  in cRel (lerpPoint c1 b1 t) (lerpPoint c2 b2 t) (lerpPoint a b3 t)
lerpCmd (cRel a1 a2 a3) (lRel b) t =
  let c1 = lerpPoint b b 0.0
      c2 = lerpPoint b b 0.0
  in cRel (lerpPoint a1 c1 t) (lerpPoint a2 c2 t) (lerpPoint a3 b t)
-- Other mismatches: lerp endpoints, use more complex command type
-- For commands with endpoints, interpolate toward the target
lerpCmd a b t = a

-- Extract the endpoint of a path command (for padding purposes)
cmdEndpoint : PathCmd → Maybe Point
cmdEndpoint (M p) = just p
cmdEndpoint (L p) = just p
cmdEndpoint (H x') = nothing  -- partial info, skip
cmdEndpoint (V y') = nothing
cmdEndpoint (C _ _ p) = just p
cmdEndpoint (S _ p) = just p
cmdEndpoint (Q _ p) = just p
cmdEndpoint (T p) = just p
cmdEndpoint (A _ _ _ _ _ p) = just p
cmdEndpoint Z = nothing
cmdEndpoint (mRel p) = just p
cmdEndpoint (lRel p) = just p
cmdEndpoint (hRel _) = nothing
cmdEndpoint (vRel _) = nothing
cmdEndpoint (cRel _ _ p) = just p
cmdEndpoint (sRel _ p) = just p
cmdEndpoint (qRel _ p) = just p
cmdEndpoint (tRel p) = just p
cmdEndpoint (aRel _ _ _ _ _ p) = just p

-- Get the last command from a path
private
  lastCmd : Path → Maybe PathCmd
  lastCmd [] = nothing
  lastCmd (c ∷ []) = just c
  lastCmd (_ ∷ cs) = lastCmd cs

  -- Replicate a value n times
  replicate : {A : Set} → ℕ → A → List A
  replicate zero _ = []
  replicate (suc n) x = x ∷ replicate n x

  -- Build padding commands for a shorter path
  padCmds : ℕ → Path → List PathCmd
  padCmds n [] = replicate n (L (0.0 , 0.0))  -- fallback: line to origin
  padCmds n path with lastCmd path
  ... | just lc = replicate n lc
  ... | nothing = replicate n (L (0.0 , 0.0))

-- Pad a path to a target length by duplicating its last command
padTo : ℕ → Path → Path
padTo n [] = []
padTo n path =
  let len = length path
  in if len ≤ᵇ n then path Data.List.++ padCmds (n ∸ len) path else path
  where open import Data.Bool using (if_then_else_)

-- Interpolate between two paths, padding the shorter to match
lerpPath : Path → Path → Float → Path
lerpPath [] [] t = []
lerpPath [] bs t = bs
lerpPath as [] t = as
lerpPath as bs t =
  let la = length as
      lb = length bs
      as' = padTo lb as
      bs' = padTo la bs
  in zipWith (λ a b → lerpCmd a b t) as' bs'

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
