{-# OPTIONS --without-K #-}

-- Secure video player: wraps PlayerConfig with signed URL support.
-- Fetches a video token from the server before loading HLS manifest,
-- then signs segment URLs using the received token.
--
-- Domain-neutral: the token endpoint is supplied by the caller as an opaque URL
-- (`initSecureModel inner tokenUrl`). A consuming domain builds its own contract —
-- e.g. the courses platform passes "/api/video-token?courseId=C&lessonId=L".

module Agdelte.Html.Controls.Video.SecurePlayer where

open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; [])

open import Agdelte.Reactive.Node.Core using (Node)
open import Agdelte.Html.Controls.Video.Types

------------------------------------------------------------------------
-- Secure config builder
------------------------------------------------------------------------

-- | Extend a VideoMsg with secure token messages.
data SecureMsg (A : Set) : Set where
  PlayerMsg      : A → SecureMsg A
  TokenReceived  : String → SecureMsg A    -- signed manifest URL
  TokenFailed    : String → SecureMsg A    -- error message
  TokenExpiring  : SecureMsg A             -- trigger refresh

-- | Secure model: wraps inner model + token state.
record SecureModel (M : Set) : Set where
  constructor mkSecureModel
  field
    smInner     : M
    smToken     : Maybe String     -- current signed manifest URL
    smTokenUrl  : String           -- endpoint to fetch token from
    smReady     : Bool             -- token obtained, player can load

open SecureModel public

-- | Create a secure PlayerConfig that signs URLs.
-- signFn: function that appends signature to a URL (obtained from server token response).
mkSecureConfig : ∀ {M A}
               → PlayerConfig M A
               → (String → String)       -- URL signing function
               → PlayerConfig M A
mkSecureConfig cfg signFn = record cfg
  { pcSignUrl = just signFn }

-- | Initial secure model wrapping an inner model. `tokenUrl` is the (opaque)
-- endpoint the player fetches its signed-manifest token from — the caller's domain
-- builds it (e.g. "/api/video-token?courseId=…&lessonId=…").
initSecureModel : ∀ {M} → M → String → SecureModel M
initSecureModel inner tokenUrl = mkSecureModel inner nothing tokenUrl false
