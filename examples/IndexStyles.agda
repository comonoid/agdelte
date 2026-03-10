{-# OPTIONS --without-K #-}

-- CSS styles for the index page (index.html)
-- Replaces the handwritten index.css
--
-- Generated via: npm run build:index-styles && npm run css:index

module IndexStyles where

open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_)

open import Agdelte.Css.Decl using (Style; _∶_)
open import Agdelte.Css.Length using (px; rem; pct; zero; auto)
open import Agdelte.Css.Color using (hex; var)
open import Agdelte.Css.Properties using (padding'; padding2; margin'; margin2;
                                          backgroundColor'; color'; fontSize';
                                          borderRadius'; gap'; maxWidth';
                                          maxHeight'; width'; height')
open import Agdelte.Css.Stylesheet using (Rule; rule; media; rawRule; Stylesheet)

------------------------------------------------------------------------
-- Section separator
------------------------------------------------------------------------

sep : String → Rule
sep label = rawRule ("/* " ++ˢ label ++ˢ " */")

------------------------------------------------------------------------
-- Body & heading
------------------------------------------------------------------------

bodyRules : Stylesheet
bodyRules =
    rule "body"
      ( "text-align" ∶ "center"
      ∷ [])
  ∷ rule "body > h1"
      ( fontSize' (rem 3.0)
      ∷ [])
  ∷ []

------------------------------------------------------------------------
-- Features badges
------------------------------------------------------------------------

featuresRules : Stylesheet
featuresRules =
    rule ".features"
      ( "display" ∶ "flex"
      ∷ gap' (rem 1.0)
      ∷ "margin" ∶ "0 auto 2rem"
      ∷ maxWidth' (px 900)
      ∷ "flex-wrap" ∶ "wrap"
      ∷ "justify-content" ∶ "center"
      ∷ [])
  ∷ rule ".feature"
      ( "background" ∶ "rgba(74, 158, 255, 0.1)"
      ∷ "border" ∶ "1px solid rgba(74, 158, 255, 0.3)"
      ∷ padding2 (rem 0.5) (rem 1.0)
      ∷ borderRadius' (px 20)
      ∷ fontSize' (rem 0.85)
      ∷ [])
  ∷ []

------------------------------------------------------------------------
-- Examples grid
------------------------------------------------------------------------

examplesGridRules : Stylesheet
examplesGridRules =
    rule ".examples"
      ( "display" ∶ "grid"
      ∷ "grid-template-columns" ∶ "repeat(auto-fill, minmax(200px, 1fr))"
      ∷ gap' (rem 1.5)
      ∷ maxWidth' (px 900)
      ∷ "margin" ∶ "0 auto 2rem"
      ∷ [])
  ∷ []

------------------------------------------------------------------------
-- Example card
------------------------------------------------------------------------

cardRules : Stylesheet
cardRules =
    rule ".example-card"
      ( "background" ∶ "var(--card)"
      ∷ borderRadius' (px 12)
      ∷ padding' (rem 1.5)
      ∷ "text-decoration" ∶ "none"
      ∷ color' (var "text")
      ∷ "text-align" ∶ "left"
      ∷ "transition" ∶ "transform 0.2s, box-shadow 0.2s"
      ∷ "box-shadow" ∶ "0 4px 20px rgba(0,0,0,0.2)"
      ∷ [])
  ∷ rule ".example-card:hover"
      ( "transform" ∶ "translateY(-4px)"
      ∷ "box-shadow" ∶ "0 8px 30px rgba(0,0,0,0.3)"
      ∷ [])
  ∷ rule ".example-card h2"
      ( color' (var "primary")
      ∷ "margin-bottom" ∶ "0.5rem"
      ∷ fontSize' (rem 1.3)
      ∷ [])
  ∷ rule ".example-card p"
      ( color' (var "muted-light")
      ∷ fontSize' (rem 0.9)
      ∷ "margin-bottom" ∶ "1rem"
      ∷ [])
  ∷ rule ".example-card .status"
      ( "display" ∶ "inline-block"
      ∷ padding2 (rem 0.25) (rem 0.75)
      ∷ borderRadius' (px 12)
      ∷ fontSize' (rem 0.75)
      ∷ "font-weight" ∶ "600"
      ∷ [])
  ∷ rule ".example-card code"
      ( "display" ∶ "block"
      ∷ "margin-top" ∶ "0.75rem"
      ∷ padding' (rem 0.5)
      ∷ "background" ∶ "rgba(0,0,0,0.3)"
      ∷ borderRadius' (px 6)
      ∷ fontSize' (rem 0.8)
      ∷ color' (var "muted")
      ∷ "overflow" ∶ "hidden"
      ∷ "text-overflow" ∶ "ellipsis"
      ∷ [])
  ∷ []

------------------------------------------------------------------------
-- Status badges
------------------------------------------------------------------------

statusRules : Stylesheet
statusRules =
    rule ".status.ready"
      ( "background" ∶ "rgba(74, 222, 128, 0.2)"
      ∷ color' (var "success")
      ∷ [])
  ∷ rule ".status.wip"
      ( "background" ∶ "rgba(251, 191, 36, 0.2)"
      ∷ color' (hex "#fbbf24")
      ∷ [])
  ∷ []

------------------------------------------------------------------------
-- Index info
------------------------------------------------------------------------

indexInfoRules : Stylesheet
indexInfoRules =
    rule ".index-info"
      ( color' (var "muted-dark")
      ∷ fontSize' (rem 0.9)
      ∷ maxWidth' (px 600)
      ∷ "margin" ∶ "0 auto"
      ∷ [])
  ∷ rule ".index-info a"
      ( color' (var "primary")
      ∷ "text-decoration" ∶ "none"
      ∷ [])
  ∷ rule ".index-info a:hover"
      ( "text-decoration" ∶ "underline"
      ∷ [])
  ∷ []

------------------------------------------------------------------------
-- Tech stack
------------------------------------------------------------------------

techStackRules : Stylesheet
techStackRules =
    rule ".tech-stack"
      ( "margin" ∶ "2rem auto 0"
      ∷ padding' (rem 1.5)
      ∷ "background" ∶ "var(--card)"
      ∷ borderRadius' (px 12)
      ∷ maxWidth' (px 600)
      ∷ "text-align" ∶ "left"
      ∷ [])
  ∷ rule ".tech-stack h3"
      ( color' (var "primary")
      ∷ "margin-bottom" ∶ "1rem"
      ∷ fontSize' (rem 1.0)
      ∷ [])
  ∷ rule ".tech-stack ul"
      ( "list-style" ∶ "none"
      ∷ "display" ∶ "grid"
      ∷ "grid-template-columns" ∶ "1fr 1fr"
      ∷ gap' (rem 0.5)
      ∷ [])
  ∷ rule ".tech-stack li"
      ( color' (var "muted-light")
      ∷ fontSize' (rem 0.85)
      ∷ [])
  ∷ rule ".tech-stack li::before"
      ( "content" ∶ "\"\\2192 \""
      ∷ color' (var "accent")
      ∷ [])
  ∷ []

------------------------------------------------------------------------
-- Combined stylesheet
------------------------------------------------------------------------

indexCSS : Stylesheet
indexCSS =
    rawRule "/* Agdelte Index Page Styles (generated from Agda) */"
  ∷ []
  ++ bodyRules
  ++ featuresRules
  ++ examplesGridRules
  ++ cardRules
  ++ statusRules
  ++ indexInfoRules
  ++ techStackRules
