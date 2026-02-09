{-# OPTIONS --without-K #-}

-- SVG Test Example
-- Basic SVG rendering test

module SvgTest where

open import Data.List using (List; []; _∷_; [_])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_)
open import Data.Unit using (⊤; tt)

open import Agdelte.Reactive.Node
open import Agdelte.Css.Color using (hex; named)
open import Agdelte.Svg

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

record Model : Set where
  constructor mkModel
  field
    radius : ℕ

------------------------------------------------------------------------
-- Messages
------------------------------------------------------------------------

data Msg : Set where
  Grow   : Msg
  Shrink : Msg

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

updateModel : Msg → Model → Model
updateModel Grow   m = mkModel (suc (Model.radius m))
updateModel Shrink m with Model.radius m
... | zero  = mkModel zero
... | suc n = mkModel n

------------------------------------------------------------------------
-- View
------------------------------------------------------------------------

svgTemplate : Node Model Msg
svgTemplate =
  div (class "svg-test" ∷ style "text-align" "center" ∷ [])
    ( h1 [] [ text "SVG Test" ]
    ∷ svg ( viewBox_ "0 0 200 200"
          ∷ width_ "200"
          ∷ height_ "200"
          ∷ [])
        ( -- Background rectangle
          rect' ( x_ "0" ∷ y_ "0"
                ∷ width_ "200" ∷ height_ "200"
                ∷ fillC (hex "#f0f0f0")
                ∷ []) []
        ∷ -- Circle with dynamic radius via binding
          circle' ( cxF 100.0 ∷ cyF 100.0
                  ∷ attrBind "r" (stringBinding λ m → show (Model.radius m))
                  ∷ fillC (hex "#4a9eff")
                  ∷ strokeC (named "white")
                  ∷ strokeWidthF 2.0
                  ∷ []) []
        ∷ -- Text
          svgText ( x_ "100" ∷ y_ "170"
                  ∷ textAnchor_ "middle"
                  ∷ fontSize_ "14"
                  ∷ fill_ "#333"
                  ∷ [])
            [ text "Click buttons below" ]
        ∷ [])
    ∷ div [ style "margin-top" "10px" ]
        ( button [ onClick Shrink ] [ text "−" ]
        ∷ button [ onClick Grow ] [ text "+" ]
        ∷ [])
    ∷ div []
        [ bind (stringBinding λ m → "Radius: " ++ show (Model.radius m)) ]
    ∷ [] )

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

svgApp : ReactiveApp Model Msg
svgApp = simpleApp (mkModel 30) updateModel svgTemplate

app : ReactiveApp Model Msg
app = svgApp
