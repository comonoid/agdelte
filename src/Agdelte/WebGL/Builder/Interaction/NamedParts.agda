{-# OPTIONS --without-K #-}

-- Interaction.NamedParts: Sub-ID picking for complex interactive objects
--
-- Allows assigning names to sub-parts of objects, enabling interaction
-- with individual components of a larger model.

module Agdelte.WebGL.Builder.Interaction.NamedParts where

open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)

open import Agdelte.WebGL.Types

------------------------------------------------------------------------
-- Named part record
------------------------------------------------------------------------

-- A named part within a larger object
record NamedPart (M Msg : Set) : Set where
  constructor namedPart
  field
    partName : String
    partNode : SceneNode M Msg

------------------------------------------------------------------------
-- Named parts constructors
------------------------------------------------------------------------

-- Create a multi-part interactive object
-- Each part has a unique name and can receive its own events
postulate
  partsGroup : ∀ {M Msg}
             → List (SceneAttr Msg)  -- Attributes for the group
             → Transform
             → List (NamedPart M Msg)
             → SceneNode M Msg

{-# COMPILE JS partsGroup = attrs => transform => parts => ({
  type: 'partsGroup',
  attrs: attrs,
  transform: transform,
  parts: parts
}) #-}

-- Handler for named part clicks
-- Receives the part name when clicked
postulate
  onPartClick : ∀ {Msg} → (String → Msg) → SceneAttr Msg

{-# COMPILE JS onPartClick = handler => ({
  type: 'onPartClick',
  handler: handler
}) #-}

-- Handler for named part hover
postulate
  onPartHover : ∀ {Msg} → (String → Msg) → SceneAttr Msg

{-# COMPILE JS onPartHover = handler => ({
  type: 'onPartHover',
  handler: handler
}) #-}

-- Handler for part leave
postulate
  onPartLeave : ∀ {Msg} → (String → Msg) → SceneAttr Msg

{-# COMPILE JS onPartLeave = handler => ({
  type: 'onPartLeave',
  handler: handler
}) #-}

------------------------------------------------------------------------
-- Convenience constructors
------------------------------------------------------------------------

-- Create a simple named part
part : ∀ {M Msg} → String → SceneNode M Msg → NamedPart M Msg
part = namedPart

-- Interactive parts group with click handler
clickableParts : ∀ {M Msg}
               → (String → Msg)
               → List (NamedPart M Msg)
               → SceneNode M Msg
clickableParts handler parts =
  partsGroup (onPartClick handler ∷ []) identityTransform parts

-- Parts group with click and hover handlers
interactiveParts : ∀ {M Msg}
                 → (String → Msg)    -- Click handler
                 → (String → Msg)    -- Hover handler
                 → (String → Msg)    -- Leave handler
                 → List (NamedPart M Msg)
                 → SceneNode M Msg
interactiveParts clickH hoverH leaveH parts =
  partsGroup (onPartClick clickH ∷ onPartHover hoverH ∷ onPartLeave leaveH ∷ [])
             identityTransform
             parts

------------------------------------------------------------------------
-- Part highlighting
------------------------------------------------------------------------

-- Highlight a specific part by name
-- The runtime will apply the highlight material to the named part
postulate
  highlightPart : ∀ {M Msg} → String → Material → SceneNode M Msg → SceneNode M Msg

{-# COMPILE JS highlightPart = partName => material => node => ({
  type: 'highlightPart',
  partName: partName,
  material: material,
  child: node
}) #-}

-- Reactive highlighting: extract the highlighted part name from model
postulate
  bindHighlight : ∀ {M Msg} → (M → Maybe String) → Material → SceneNode M Msg → SceneNode M Msg

{-# COMPILE JS bindHighlight = extract => material => node => ({
  type: 'bindHighlight',
  extract: extract,
  material: material,
  child: node
}) #-}
