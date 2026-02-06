{-# OPTIONS --without-K #-}

-- SVG Transform DSL
-- Typed transforms with rendering to SVG transform attribute

module Agdelte.Svg.Transform where

open import Data.Float using (Float)
open import Data.List using (List; []; _∷_; map; foldl)
open import Data.String using (String; _++_)
open import Function using (_∘_)

open import Agdelte.Css.Show using (showFloat)
open import Agdelte.Svg.Path using (Point; x; y)

------------------------------------------------------------------------
-- Transform type
------------------------------------------------------------------------

data Transform : Set where
  translate : Float → Float → Transform
  rotate    : Float → Transform                    -- degrees, around origin
  rotateAt  : Float → Float → Float → Transform    -- degrees, cx, cy
  scale     : Float → Float → Transform
  scaleU    : Float → Transform                    -- uniform scale
  skewX     : Float → Transform                    -- degrees
  skewY     : Float → Transform                    -- degrees
  matrix    : Float → Float → Float → Float → Float → Float → Transform  -- a b c d e f

Transforms : Set
Transforms = List Transform

------------------------------------------------------------------------
-- Rendering
------------------------------------------------------------------------

showTransform : Transform → String
showTransform (translate tx ty)    = "translate(" ++ showFloat tx ++ " " ++ showFloat ty ++ ")"
showTransform (rotate deg)         = "rotate(" ++ showFloat deg ++ ")"
showTransform (rotateAt deg cx cy) = "rotate(" ++ showFloat deg ++ " " ++ showFloat cx ++ " " ++ showFloat cy ++ ")"
showTransform (scale sx sy)        = "scale(" ++ showFloat sx ++ " " ++ showFloat sy ++ ")"
showTransform (scaleU s)           = "scale(" ++ showFloat s ++ ")"
showTransform (skewX deg)          = "skewX(" ++ showFloat deg ++ ")"
showTransform (skewY deg)          = "skewY(" ++ showFloat deg ++ ")"
showTransform (matrix a b c d e f) =
  "matrix(" ++ showFloat a ++ " " ++ showFloat b ++ " " ++
               showFloat c ++ " " ++ showFloat d ++ " " ++
               showFloat e ++ " " ++ showFloat f ++ ")"

-- Render transform list to SVG transform attribute
renderTransforms : Transforms → String
renderTransforms [] = ""
renderTransforms (t ∷ []) = showTransform t
renderTransforms (t ∷ ts) = showTransform t ++ " " ++ renderTransforms ts

------------------------------------------------------------------------
-- Common transform combinations
------------------------------------------------------------------------

-- Translate by Point
translatePt : Point → Transform
translatePt p = translate (x p) (y p)

-- Rotate around a point
rotateAround : Float → Point → Transform
rotateAround deg p = rotateAt deg (x p) (y p)

-- Scale uniformly from center
scaleAt : Float → Point → Transforms
scaleAt s center =
  translate (x center) (y center)
  ∷ scaleU s
  ∷ translate (- x center) (- y center)
  ∷ []
  where
    open import Data.Float using (-_)

------------------------------------------------------------------------
-- Attribute helper
------------------------------------------------------------------------

open import Agdelte.Reactive.Node using (Attr; attr)

-- Create transform attribute from Transform list
transform' : ∀ {M Msg} → Transforms → Attr M Msg
transform' ts = attr "transform" (renderTransforms ts)

-- Create transform attribute from single Transform
transformOne : ∀ {M Msg} → Transform → Attr M Msg
transformOne t = attr "transform" (showTransform t)
