{-# OPTIONS --without-K #-}

-- SVG Timeline
-- Events along a time axis

module Agdelte.Svg.Controls.Charts.Timeline where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; _≤ᵇ_; _<ᵇ_; fromℕ)
open import Data.List as List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; text; on)
open import Agdelte.Svg.Elements using (svg; g; rect'; circle'; line'; svgText)
open import Agdelte.Svg.Attributes
open import Agdelte.Css.Show using (showFloat)
open import Function using (case_of_)

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

  -- Label collision avoidance threshold (pixels)
  labelThreshold : Float
  labelThreshold = 60.0

  absFloat : Float → Float
  absFloat v = if v <ᵇ 0.0 then 0.0 - v else v

------------------------------------------------------------------------
-- Horizontal Timeline
------------------------------------------------------------------------

-- | Horizontal timeline
horizontalTimeline : ∀ {M A}
                   → Float → Float → Float → Float  -- x, y, width, height
                   → List (TimelineEvent A)
                   → Node M A
horizontalTimeline {M} {A} px py w h [] = g [] []
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

    renderEvent : Float → Float → Float → Float → Float
                → Float → TimelineEvent A → List (Node M A)
    renderEvent bx axY w' minT maxT labelYOff e =
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
      in marker
         ∷ svgText ( xF ex
                   ∷ yF (axY + labelYOff)
                   ∷ attr "text-anchor" "middle"
                   ∷ attr "font-size" "12"
                   ∷ [] )
             ( text (evLabel e) ∷ [] )
         ∷ []
      where

    -- Check if current event is too close to the previous one
    -- and stagger labels: even-indexed labels go above, odd go below
    collectEvents : Float → Float → Float → Float → Float
                  → List (TimelineEvent A) → Float → ℕ → List (Node M A)
    collectEvents _ _ _ _ _ [] _ _ = []
    collectEvents bx axY w' minT maxT (e ∷ es) prevPos idx =
      let ex = bx + scaleT minT maxT w' (evTime e)
          tooClose = absFloat (ex - prevPos) <ᵇ labelThreshold
          -- Default offset is above the axis (-20); stagger to below (+25) for odd
          labelYOff = if tooClose
                      then (if isEven idx then 0.0 - 20.0 else 25.0)
                      else 0.0 - 20.0
      in renderEvent bx axY w' minT maxT labelYOff e
         List.++ (collectEvents bx axY w' minT maxT es ex (suc idx))
      where
        open import Data.Nat using (_≡ᵇ_)
        isEven : ℕ → Bool
        isEven zero = true
        isEven (suc zero) = false
        isEven (suc (suc n)) = isEven n

    renderEvents : Float → Float → Float → Float → Float
                 → List (TimelineEvent A) → Node M A
    renderEvents bx axY w' minT maxT events' =
      g [] (collectEvents bx axY w' minT maxT events' (0.0 - 1.0e10) 0)

------------------------------------------------------------------------
-- Vertical Timeline
------------------------------------------------------------------------

-- | Vertical timeline
verticalTimeline : ∀ {M A}
                 → Float → Float → Float → Float
                 → List (TimelineEvent A)
                 → Node M A
verticalTimeline {M} {A} px py w h [] = g [] []
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

------------------------------------------------------------------------
-- Zoomable Timeline
------------------------------------------------------------------------

open import Agdelte.Svg.ViewBox using (ViewBox; viewBoxBind; showViewBox)

-- | Zoomable/pannable horizontal timeline.
--   Wraps the timeline in an SVG with a dynamic viewBox.
--   The caller provides:
--   - a projection from model to ViewBox (for current pan/zoom state)
--   - the inner timeline content dimensions (used as the SVG width/height attributes)
--   - the list of events
zoomableTimeline : ∀ {M A}
                 → (M → ViewBox)            -- viewBox state projection
                 → Float → Float            -- SVG element width, height
                 → Float → Float            -- inner content width, height
                 → List (TimelineEvent A)
                 → Node M A
zoomableTimeline {M} {A} getVB svgW svgH contentW contentH events =
  svg ( widthF svgW
      ∷ heightF svgH
      ∷ viewBoxBind getVB
      ∷ attr "class" "svg-timeline-zoomable"
      ∷ [] )
    ( horizontalTimeline 0.0 0.0 contentW contentH events
    ∷ [] )
