{-# OPTIONS --without-K #-}

-- MediaSource lifecycle helpers.
-- Provides init command and buffer state query.

module Agdelte.Html.Controls.Video.Source where

open import Data.String using (String)

open import Agdelte.Core.Cmd as Cmd using (Cmd; httpGet)
open import Agdelte.Html.Controls.Video.Types
open import Agdelte.Html.Controls.Video.SegmentLoader using (signUrl)

------------------------------------------------------------------------
-- Init helper — fetch manifest on player load
------------------------------------------------------------------------

-- | Request manifest, called from the consumer's cmd on init.
initVideoSource : ∀ {M A} → PlayerConfig M A → Cmd VideoMsg
initVideoSource cfg =
  httpGet (signUrl cfg (pcManifestUrl cfg)) ManifestLoaded ManifestError

------------------------------------------------------------------------
-- Buffer state query (JS postulate)
------------------------------------------------------------------------

-- | Get the furthest buffered time for the video element
postulate getBufferedEnd : String → String
{-# COMPILE JS getBufferedEnd = function(sel) {
  var el = document.querySelector(sel);
  if (el && el.buffered && el.buffered.length > 0)
    return String(el.buffered.end(el.buffered.length - 1));
  return "0";
} #-}
