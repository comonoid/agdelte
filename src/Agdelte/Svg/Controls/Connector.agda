{-# OPTIONS --without-K #-}

-- SvgConnector: lines connecting elements
-- For flowcharts, diagrams, node graphs

module Agdelte.Svg.Controls.Connector where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; _<ᵇ_)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; text)
open import Agdelte.Svg.Elements using (g; circle')
open import Agdelte.Svg.Attributes
  hiding (x_; y_)
  renaming (cxF to attrCx; cyF to attrCy)
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Connector Type
------------------------------------------------------------------------

data ConnectorType : Set where
  Straight   : ConnectorType   -- direct line
  Curved     : ConnectorType   -- bezier curve
  Orthogonal : ConnectorType   -- right-angle turns

------------------------------------------------------------------------
-- Connector Style
------------------------------------------------------------------------

record ConnectorStyle : Set where
  constructor mkConnectorStyle
  field
    lineColor     : String
    lineWidth     : Float
    dashPattern   : String     -- e.g. "5,5" or "" for solid
    arrowSize     : Float      -- 0 for no arrow
    dotRadius     : Float      -- 0 for no endpoint dots

open ConnectorStyle public

defaultConnectorStyle : ConnectorStyle
defaultConnectorStyle = mkConnectorStyle
  "#6b7280"    -- gray
  2.0
  ""           -- solid
  8.0          -- arrow
  0.0          -- no dots

dashedConnectorStyle : ConnectorStyle
dashedConnectorStyle = mkConnectorStyle
  "#6b7280"
  2.0
  "5,5"        -- dashed
  0.0          -- no arrow
  0.0

arrowConnectorStyle : ConnectorStyle
arrowConnectorStyle = mkConnectorStyle
  "#3b82f6"    -- blue
  2.0
  ""
  10.0         -- arrow
  0.0

dottedConnectorStyle : ConnectorStyle
dottedConnectorStyle = mkConnectorStyle
  "#9ca3af"
  2.0
  ""
  0.0
  4.0          -- endpoint dots

------------------------------------------------------------------------
-- Arrow marker definition (must be in defs)
------------------------------------------------------------------------

-- Arrow marker for end of line
svgArrowMarker : ∀ {M Msg}
               → String        -- marker id
               → String        -- color
               → Float         -- size
               → Node M Msg
svgArrowMarker markerId color size =
  elem "marker" ( attr "id" markerId
                ∷ attr "viewBox" "0 0 10 10"
                ∷ attr "refX" "9"
                ∷ attr "refY" "5"
                ∷ attr "markerWidth" (showFloat size)
                ∷ attr "markerHeight" (showFloat size)
                ∷ attr "orient" "auto-start-reverse"
                ∷ [] )
    ( elem "path" ( d_ "M 0 0 L 10 5 L 0 10 z"
                  ∷ fill_ color
                  ∷ [] ) []
    ∷ [] )

------------------------------------------------------------------------
-- Straight Connector
------------------------------------------------------------------------

svgConnectorStraight : ∀ {M Msg}
                     → Float → Float → Float → Float  -- x1, y1, x2, y2
                     → ConnectorStyle
                     → Node M Msg
svgConnectorStraight x1 y1 x2 y2 sty =
  g ( attr "class" "svg-connector-straight" ∷ [] )
    ( elem "line" ( attr "x1" (showFloat x1)
                  ∷ attr "y1" (showFloat y1)
                  ∷ attr "x2" (showFloat x2)
                  ∷ attr "y2" (showFloat y2)
                  ∷ stroke_ (lineColor sty)
                  ∷ strokeWidthF (lineWidth sty)
                  ∷ attr "stroke-dasharray" (let dp = dashPattern sty
                                             in if isEmpty dp then "none" else dp)
                  ∷ [] ) []
    ∷ [] )
  where
    isEmpty : String → Bool
    isEmpty "" = true
    isEmpty _ = false

------------------------------------------------------------------------
-- Curved Connector (Bezier)
------------------------------------------------------------------------

svgConnectorCurved : ∀ {M Msg}
                   → Float → Float → Float → Float  -- x1, y1, x2, y2
                   → ConnectorStyle
                   → Node M Msg
svgConnectorCurved x1 y1 x2 y2 sty =
  let -- Control points for smooth curve
      dx = x2 - x1
      cp1x = x1 + dx * 0.5
      cp1y = y1
      cp2x = x1 + dx * 0.5
      cp2y = y2
      pathD = "M " ++ showFloat x1 ++ " " ++ showFloat y1
           ++ " C " ++ showFloat cp1x ++ " " ++ showFloat cp1y
           ++ ", " ++ showFloat cp2x ++ " " ++ showFloat cp2y
           ++ ", " ++ showFloat x2 ++ " " ++ showFloat y2
  in g ( attr "class" "svg-connector-curved" ∷ [] )
       ( elem "path" ( d_ pathD
                     ∷ fill_ "none"
                     ∷ stroke_ (lineColor sty)
                     ∷ strokeWidthF (lineWidth sty)
                     ∷ [] ) []
       ∷ [] )

------------------------------------------------------------------------
-- Orthogonal Connector (right angles)
------------------------------------------------------------------------

svgConnectorOrthogonal : ∀ {M Msg}
                       → Float → Float → Float → Float  -- x1, y1, x2, y2
                       → ConnectorStyle
                       → Node M Msg
svgConnectorOrthogonal x1 y1 x2 y2 sty =
  let -- Create path with right angles
      midX = (x1 + x2) ÷ 2.0
      pathD = "M " ++ showFloat x1 ++ " " ++ showFloat y1
           ++ " L " ++ showFloat midX ++ " " ++ showFloat y1
           ++ " L " ++ showFloat midX ++ " " ++ showFloat y2
           ++ " L " ++ showFloat x2 ++ " " ++ showFloat y2
  in g ( attr "class" "svg-connector-ortho" ∷ [] )
       ( elem "path" ( d_ pathD
                     ∷ fill_ "none"
                     ∷ stroke_ (lineColor sty)
                     ∷ strokeWidthF (lineWidth sty)
                     ∷ [] ) []
       ∷ [] )

------------------------------------------------------------------------
-- Generic Connector
------------------------------------------------------------------------

svgConnector : ∀ {M Msg}
             → Float → Float → Float → Float
             → ConnectorType
             → ConnectorStyle
             → Node M Msg
svgConnector x1 y1 x2 y2 Straight sty = svgConnectorStraight x1 y1 x2 y2 sty
svgConnector x1 y1 x2 y2 Curved sty = svgConnectorCurved x1 y1 x2 y2 sty
svgConnector x1 y1 x2 y2 Orthogonal sty = svgConnectorOrthogonal x1 y1 x2 y2 sty

------------------------------------------------------------------------
-- Simple Connectors
------------------------------------------------------------------------

svgLine : ∀ {M Msg}
        → Float → Float → Float → Float
        → Node M Msg
svgLine x1 y1 x2 y2 = svgConnectorStraight x1 y1 x2 y2 defaultConnectorStyle

svgArrowLine : ∀ {M Msg}
             → Float → Float → Float → Float
             → Node M Msg
svgArrowLine x1 y1 x2 y2 = svgConnectorStraight x1 y1 x2 y2 arrowConnectorStyle

svgDashedLine : ∀ {M Msg}
              → Float → Float → Float → Float
              → Node M Msg
svgDashedLine x1 y1 x2 y2 = svgConnectorStraight x1 y1 x2 y2 dashedConnectorStyle
