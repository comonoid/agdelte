{-# OPTIONS --without-K #-}

-- Segment fetching pipeline: URL → [sign] → fetch → base64 data.
-- Isolated from Source so that authentication, decryption, and
-- variant selection can be injected as middleware.

module Agdelte.Html.Controls.Video.SegmentLoader where

open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)

open import Agdelte.Core.Task as Task using (Task; fetchBinary)
open import Agdelte.Html.Controls.Video.Types

------------------------------------------------------------------------
-- URL signing
------------------------------------------------------------------------

-- | Apply URL signing if configured, identity otherwise.
signUrl : ∀ {M A} → PlayerConfig M A → String → String
signUrl cfg url with pcSignUrl cfg
... | nothing   = url
... | just sign = sign url

------------------------------------------------------------------------
-- Segment fetch pipeline
------------------------------------------------------------------------

-- | Full pipeline: build URL → [sign] → fetch → base64 data.
-- Steps in brackets are no-ops by default and activate when protection
-- is enabled (see PROTECTION.md).
loadSegment : ∀ {M A} → PlayerConfig M A → String → Task String
loadSegment cfg url = fetchBinary (signUrl cfg url)
