{-# OPTIONS --without-K #-}

-- SVG Path DSL
-- Typed path commands with compile-time validation

module Agdelte.Svg.Path where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Float using (Float; _+_; _-_; _*_; _÷_)
open import Data.List using (List; []; _∷_; map; foldl; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.String using (String; _++_)
open import Function using (_∘_)

open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Point
------------------------------------------------------------------------

record Point : Set where
  constructor _,_
  field
    x : Float
    y : Float

open Point public

showPt : Point → String
showPt p = showFloat (x p) ++ " " ++ showFloat (y p)

------------------------------------------------------------------------
-- Path Commands
------------------------------------------------------------------------

data PathCmd : Set where
  -- Absolute commands (uppercase in SVG)
  M : Point → PathCmd                                    -- moveTo
  L : Point → PathCmd                                    -- lineTo
  H : Float → PathCmd                                    -- horizontal line
  V : Float → PathCmd                                    -- vertical line
  C : Point → Point → Point → PathCmd                    -- cubic bezier
  S : Point → Point → PathCmd                            -- smooth cubic
  Q : Point → Point → PathCmd                            -- quadratic bezier
  T : Point → PathCmd                                    -- smooth quadratic
  A : Float → Float → Float → Bool → Bool → Point → PathCmd  -- arc
  Z : PathCmd                                            -- closePath

  -- Relative commands (lowercase in SVG)
  mRel : Point → PathCmd
  lRel : Point → PathCmd
  hRel : Float → PathCmd
  vRel : Float → PathCmd
  cRel : Point → Point → Point → PathCmd
  sRel : Point → Point → PathCmd
  qRel : Point → Point → PathCmd
  tRel : Point → PathCmd
  aRel : Float → Float → Float → Bool → Bool → Point → PathCmd

Path : Set
Path = List PathCmd

------------------------------------------------------------------------
-- Rendering
------------------------------------------------------------------------

private
  flag : Bool → String
  flag true  = "1"
  flag false = "0"

showCmd : PathCmd → String
showCmd (M p)              = "M" ++ showPt p
showCmd (L p)              = "L" ++ showPt p
showCmd (H x')             = "H" ++ showFloat x'
showCmd (V y')             = "V" ++ showFloat y'
showCmd (C c1 c2 p)        = "C" ++ showPt c1 ++ " " ++ showPt c2 ++ " " ++ showPt p
showCmd (S c2 p)           = "S" ++ showPt c2 ++ " " ++ showPt p
showCmd (Q c p)            = "Q" ++ showPt c ++ " " ++ showPt p
showCmd (T p)              = "T" ++ showPt p
showCmd (A rx ry rot lrg sw p) =
  "A" ++ showFloat rx ++ " " ++ showFloat ry ++ " " ++ showFloat rot
      ++ " " ++ flag lrg ++ " " ++ flag sw ++ " " ++ showPt p
showCmd Z                  = "Z"
-- Relative
showCmd (mRel p)           = "m" ++ showPt p
showCmd (lRel p)           = "l" ++ showPt p
showCmd (hRel x')          = "h" ++ showFloat x'
showCmd (vRel y')          = "v" ++ showFloat y'
showCmd (cRel c1 c2 p)     = "c" ++ showPt c1 ++ " " ++ showPt c2 ++ " " ++ showPt p
showCmd (sRel c2 p)        = "s" ++ showPt c2 ++ " " ++ showPt p
showCmd (qRel c p)         = "q" ++ showPt c ++ " " ++ showPt p
showCmd (tRel p)           = "t" ++ showPt p
showCmd (aRel rx ry rot lrg sw p) =
  "a" ++ showFloat rx ++ " " ++ showFloat ry ++ " " ++ showFloat rot
      ++ " " ++ flag lrg ++ " " ++ flag sw ++ " " ++ showPt p

-- Render path to SVG d attribute string
renderPath : Path → String
renderPath [] = ""
renderPath (c ∷ []) = showCmd c
renderPath (c ∷ cs) = showCmd c ++ " " ++ renderPath cs

------------------------------------------------------------------------
-- Point operations
------------------------------------------------------------------------

addPt : Point → Point → Point
addPt a b = (x a + x b) , (y a + y b)

subPt : Point → Point → Point
subPt a b = (x a - x b) , (y a - y b)

scalePt : Float → Point → Point
scalePt s p = (s * x p) , (s * y p)

-- Distance between two points
dist : Point → Point → Float
dist a b = sqrt ((x b - x a) * (x b - x a) + (y b - y a) * (y b - y a))
  where
    postulate sqrt : Float → Float
    {-# COMPILE JS sqrt = Math.sqrt #-}

------------------------------------------------------------------------
-- Path combinators
------------------------------------------------------------------------

-- Translate all points in a path
translatePath : Float → Float → Path → Path
translatePath dx dy = map translateCmd
  where
    shift : Point → Point
    shift p = (x p + dx) , (y p + dy)

    translateCmd : PathCmd → PathCmd
    translateCmd (M p)              = M (shift p)
    translateCmd (L p)              = L (shift p)
    translateCmd (H x')             = H (x' + dx)
    translateCmd (V y')             = V (y' + dy)
    translateCmd (C c1 c2 p)        = C (shift c1) (shift c2) (shift p)
    translateCmd (S c2 p)           = S (shift c2) (shift p)
    translateCmd (Q c p)            = Q (shift c) (shift p)
    translateCmd (T p)              = T (shift p)
    translateCmd (A rx ry rot l s p) = A rx ry rot l s (shift p)
    translateCmd Z                  = Z
    -- Relative commands: don't shift (they're relative)
    translateCmd cmd                = cmd

-- Scale all points in a path
scalePath : Float → Float → Path → Path
scalePath sx sy = map scaleCmd
  where
    scale : Point → Point
    scale p = (x p * sx) , (y p * sy)

    scaleCmd : PathCmd → PathCmd
    scaleCmd (M p)              = M (scale p)
    scaleCmd (L p)              = L (scale p)
    scaleCmd (H x')             = H (x' * sx)
    scaleCmd (V y')             = V (y' * sy)
    scaleCmd (C c1 c2 p)        = C (scale c1) (scale c2) (scale p)
    scaleCmd (S c2 p)           = S (scale c2) (scale p)
    scaleCmd (Q c p)            = Q (scale c) (scale p)
    scaleCmd (T p)              = T (scale p)
    scaleCmd (A rx ry rot l s p) = A (rx * sx) (ry * sy) rot l s (scale p)
    scaleCmd Z                  = Z
    -- Relative commands
    scaleCmd (mRel p)           = mRel (scale p)
    scaleCmd (lRel p)           = lRel (scale p)
    scaleCmd (hRel x')          = hRel (x' * sx)
    scaleCmd (vRel y')          = vRel (y' * sy)
    scaleCmd (cRel c1 c2 p)     = cRel (scale c1) (scale c2) (scale p)
    scaleCmd (sRel c2 p)        = sRel (scale c2) (scale p)
    scaleCmd (qRel c p)         = qRel (scale c) (scale p)
    scaleCmd (tRel p)           = tRel (scale p)
    scaleCmd (aRel rx ry rot l s p) = aRel (rx * sx) (ry * sy) rot l s (scale p)

-- Close a path (ensure Z at end)
closePath : Path → Path
closePath [] = Z ∷ []
closePath (Z ∷ []) = Z ∷ []
closePath (c ∷ cs) = c ∷ closePath cs

------------------------------------------------------------------------
-- Path length estimation
------------------------------------------------------------------------

-- Absolute value of Float
private
  postulate absF : Float → Float
  {-# COMPILE JS absF = Math.abs #-}

-- Estimate segment length (exact for L/H/V, approximate for curves)
private
  -- Rough approximation: for C, use control polygon length * 0.75
  -- For Q, use control polygon length * 0.8
  -- For A, use chord length (rough)
  cmdLength : Point → PathCmd → Float
  cmdLength curr (L p)      = dist curr p
  cmdLength curr (H x')     = absF (x' - x curr)
  cmdLength curr (V y')     = absF (y' - y curr)
  cmdLength curr (C c1 c2 p) = (dist curr c1 + dist c1 c2 + dist c2 p) * 0.75
  cmdLength curr (S c2 p)   = (dist curr c2 + dist c2 p) * 0.8
  cmdLength curr (Q c p)    = (dist curr c + dist c p) * 0.8
  cmdLength curr (T p)      = dist curr p  -- rough
  cmdLength curr (A rx ry _ _ _ p) = dist curr p  -- chord length (very rough)
  cmdLength _ _             = 0.0

  -- Track current position while accumulating length
  accumLength : (Point × Float) → PathCmd → (Point × Float)
  accumLength (curr , len) (M p)       = (p , len)
  accumLength (curr , len) (L p)       = (p , len + cmdLength curr (L p))
  accumLength (curr , len) (H x')      = ((x' , y curr) , len + cmdLength curr (H x'))
  accumLength (curr , len) (V y')      = ((x curr , y') , len + cmdLength curr (V y'))
  accumLength (curr , len) (C _ _ p)   = (p , len + cmdLength curr (C (0.0 , 0.0) (0.0 , 0.0) p))
  accumLength (curr , len) (S _ p)     = (p , len + cmdLength curr (S (0.0 , 0.0) p))
  accumLength (curr , len) (Q _ p)     = (p , len + cmdLength curr (Q (0.0 , 0.0) p))
  accumLength (curr , len) (T p)       = (p , len + cmdLength curr (T p))
  accumLength (curr , len) (A rx ry rot l s p) = (p , len + cmdLength curr (A rx ry rot l s p))
  accumLength (curr , len) Z           = (curr , len)
  -- Relative: add to current position
  accumLength (curr , len) (mRel p)    = (addPt curr p , len)
  accumLength (curr , len) (lRel p)    = let np = addPt curr p in (np , len + dist curr np)
  accumLength (curr , len) (hRel dx)   = let np = (x curr + dx , y curr) in (np , len + dist curr np)
  accumLength (curr , len) (vRel dy)   = let np = (x curr , y curr + dy) in (np , len + dist curr np)
  accumLength (curr , len) (cRel _ _ p) = let np = addPt curr p in (np , len + dist curr np * 0.75)
  accumLength (curr , len) (sRel _ p)   = let np = addPt curr p in (np , len + dist curr np * 0.8)
  accumLength (curr , len) (qRel _ p)   = let np = addPt curr p in (np , len + dist curr np * 0.8)
  accumLength (curr , len) (tRel p)     = let np = addPt curr p in (np , len + dist curr np)
  accumLength (curr , len) (aRel _ _ _ _ _ p) = let np = addPt curr p in (np , len + dist curr np)

-- Estimate total path length
pathLength : Path → Float
pathLength cmds = proj₂ (foldl accumLength ((0.0 , 0.0) , 0.0) cmds)
