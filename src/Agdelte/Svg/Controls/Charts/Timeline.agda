{-# OPTIONS --without-K #-}

-- SVG Timeline
-- Events along a time axis

module Agdelte.Svg.Controls.Charts.Timeline where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; _≤ᵇ_; _<ᵇ_; fromℕ)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; text; on)
open import Agdelte.Svg.Elements using (svg; g; rect'; circle'; line'; svgText)
open import Agdelte.Svg.Attributes
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Data types
------------------------------------------------------------------------

record TimelineEvent (A : Set) : Set where
  constructor mkTimelineEvent
  field
    evTime    : Float           -- position on timeline
    evLabel   : String
    evDetail  : Maybe String
    evColor   : String
    evOnClick : Maybe A

open TimelineEvent public

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

private
  findMinMax : ∀ {A} → List (TimelineEvent A) → Float → Float → Float × Float
  findMinMax [] minA maxA = (minA , maxA)
  findMinMax (e ∷ es) minA maxA =
    findMinMax es
      (if evTime e <ᵇ minA then evTime e else minA)
      (if maxA <ᵇ evTime e then evTime e else maxA)
    where
      open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Horizontal Timeline
------------------------------------------------------------------------

-- | Horizontal timeline
horizontalTimeline : ∀ {M A}
                   → Float → Float → Float → Float  -- x, y, width, height
                   → List (TimelineEvent A)
                   → Node M A
horizontalTimeline {M} {A} px py w h events =
  let (minT , maxT) = findMinMax events 1.0e10 (0.0 - 1.0e10)
      axisY = py + h ÷ 2.0
  in g ( attr "class" "svg-timeline" ∷ [] )
       ( -- Main axis line
         line' ( x1F px ∷ y1F axisY
               ∷ x2F (px + w) ∷ y2F axisY
               ∷ stroke_ "#cbd5e1"
               ∷ strokeWidthF 2.0
               ∷ [] ) []
       -- Events
       ∷ renderEvents px axisY w minT maxT events
       ∷ [] )
  where
    open import Data.Product using (_×_; _,_)

    scaleT : Float → Float → Float → Float → Float
    scaleT minT maxT w' t =
      let range = if (maxT - minT) ≤ᵇ 0.0 then 1.0 else maxT - minT
      in ((t - minT) ÷ range) * w'

    renderEvents : Float → Float → Float → Float → Float
                 → List (TimelineEvent A) → Node M A
    renderEvents _ _ _ _ _ [] = g [] []
    renderEvents bx axY w' minT maxT (e ∷ es) =
      let ex = bx + scaleT minT maxT w' (evTime e)
          marker = case evOnClick e of λ where
            nothing →
              circle' ( cxF ex ∷ cyF axY
                      ∷ rF 8.0
                      ∷ fill_ (evColor e)
                      ∷ stroke_ "white"
                      ∷ strokeWidthF 2.0
                      ∷ attr "class" "timeline-event"
                      ∷ [] ) []
            (just msg) →
              circle' ( cxF ex ∷ cyF axY
                      ∷ rF 8.0
                      ∷ fill_ (evColor e)
                      ∷ stroke_ "white"
                      ∷ strokeWidthF 2.0
                      ∷ attr "class" "timeline-event timeline-event--clickable"
                      ∷ attr "style" "cursor: pointer"
                      ∷ on "click" msg
                      ∷ [] ) []
      in g []
           ( marker
           -- Label
           ∷ svgText ( xF ex
                     ∷ yF (axY - 20.0)
                     ∷ attr "text-anchor" "middle"
                     ∷ attr "font-size" "12"
                     ∷ [] )
               ( text (evLabel e) ∷ [] )
           ∷ renderEvents bx axY w' minT maxT es
           ∷ [] )
      where
        case_of_ : ∀ {a b} {X : Set a} {Y : Set b} → X → (X → Y) → Y
        case x of f = f x

------------------------------------------------------------------------
-- Vertical Timeline
------------------------------------------------------------------------

-- | Vertical timeline
verticalTimeline : ∀ {M A}
                 → Float → Float → Float → Float
                 → List (TimelineEvent A)
                 → Node M A
verticalTimeline {M} {A} px py w h events =
  let (minT , maxT) = findMinMax events 1.0e10 (0.0 - 1.0e10)
      axisX = px + w ÷ 2.0
  in g ( attr "class" "svg-timeline-vertical" ∷ [] )
       ( -- Main axis line
         line' ( x1F axisX ∷ y1F py
               ∷ x2F axisX ∷ y2F (py + h)
               ∷ stroke_ "#cbd5e1"
               ∷ strokeWidthF 2.0
               ∷ [] ) []
       -- Events
       ∷ renderEventsV axisX py h minT maxT events true
       ∷ [] )
  where
    open import Data.Product using (_×_; _,_)

    scaleT : Float → Float → Float → Float → Float
    scaleT minT maxT h' t =
      let range = if (maxT - minT) ≤ᵇ 0.0 then 1.0 else maxT - minT
      in ((t - minT) ÷ range) * h'

    renderEventsV : Float → Float → Float → Float → Float
                  → List (TimelineEvent A) → Bool → Node M A
    renderEventsV _ _ _ _ _ [] _ = g [] []
    renderEventsV axX by h' minT maxT (e ∷ es) leftSide =
      let ey = by + scaleT minT maxT h' (evTime e)
          labelX = if leftSide then axX - 20.0 else axX + 20.0
          anchor = if leftSide then "end" else "start"
      in g []
           ( -- Event marker
             circle' ( cxF axX ∷ cyF ey
                     ∷ rF 8.0
                     ∷ fill_ (evColor e)
                     ∷ stroke_ "white"
                     ∷ strokeWidthF 2.0
                     ∷ [] ) []
           -- Label
           ∷ svgText ( xF labelX
                     ∷ yF ey
                     ∷ attr "text-anchor" anchor
                     ∷ attr "dominant-baseline" "middle"
                     ∷ attr "font-size" "12"
                     ∷ [] )
               ( text (evLabel e) ∷ [] )
           ∷ renderEventsV axX by h' minT maxT es (not leftSide)
           ∷ [] )
      where
        not : Bool → Bool
        not true = false
        not false = true

------------------------------------------------------------------------
-- Simple constructors
------------------------------------------------------------------------

-- | Simple timeline from (time, label) pairs
simpleTimeline : ∀ {M A}
               → Float → Float → Float → Float
               → Bool                          -- horizontal?
               → List (Float × String)
               → Node M A
simpleTimeline {M} {A} px py w h horiz pairs =
  let events = toEvents pairs
  in if horiz
     then horizontalTimeline px py w h events
     else verticalTimeline px py w h events
  where
    toEvents : List (Float × String) → List (TimelineEvent A)
    toEvents [] = []
    toEvents ((t , lbl) ∷ rest) =
      mkTimelineEvent t lbl nothing "#3b82f6" nothing
      ∷ toEvents rest
