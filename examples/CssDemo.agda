{-# OPTIONS --without-K #-}

-- CssDemo: test module for generate-css.js

module CssDemo where

open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)

open import Agdelte.Css.Decl using (Decl; Style; _∶_)
open import Agdelte.Css.Stylesheet

appCSS : Stylesheet
appCSS =
    rawRule "@charset \"UTF-8\";"
  ∷ rule ".card" (
        "padding"       ∶ "16px"
      ∷ "background"    ∶ "#fff"
      ∷ "border-radius" ∶ "8px"
      ∷ "transition"    ∶ "box-shadow 0.2s, transform 0.2s"
      ∷ "cursor"        ∶ "pointer"
      ∷ [])
  ∷ rule ".card:hover" (
        "box-shadow" ∶ "0 8px 24px rgba(0,0,0,0.3)"
      ∷ "transform"  ∶ "translateY(-2px)"
      ∷ [])
  ∷ media "(max-width: 768px)" (
        rule ".card" (
            "padding" ∶ "8px"
          ∷ [])
      ∷ [])
  ∷ keyframe "fadeIn" (
        ("from" , "opacity" ∶ "0" ∷ [])
      ∷ ("to"   , "opacity" ∶ "1" ∷ [])
      ∷ [])
  ∷ []
