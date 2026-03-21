{-# OPTIONS --without-K #-}

-- SEO: Document head management (title, meta tags, canonical URL).
-- Exposes postulated Cmd constructors backed by JS FFI.

module Agdelte.Html.Head where

open import Data.String using (String; _++_)
open import Data.Nat using (ℕ)

open import Agdelte.Core.Cmd using (Cmd; setProp)

------------------------------------------------------------------------
-- Head manipulation via setProp on document-level elements
------------------------------------------------------------------------

-- | Set document title.
-- Uses setProp on "title" element (first <title> in head).
setTitle : ∀ {A} → String → Cmd A
setTitle t = setProp "head > title" "textContent" t

-- | Set meta description.
setDescription : ∀ {A} → String → Cmd A
setDescription d = setProp "meta[name=description]" "content" d

-- | Set canonical URL.
setCanonical : ∀ {A} → String → Cmd A
setCanonical url = setProp "link[rel=canonical]" "href" url

-- | Set Open Graph title.
setOgTitle : ∀ {A} → String → Cmd A
setOgTitle t = setProp "meta[property='og:title']" "content" t

-- | Set Open Graph description.
setOgDescription : ∀ {A} → String → Cmd A
setOgDescription d = setProp "meta[property='og:description']" "content" d

-- | Set Open Graph image.
setOgImage : ∀ {A} → String → Cmd A
setOgImage url = setProp "meta[property='og:image']" "content" url

------------------------------------------------------------------------
-- Batch: set all SEO tags for a course page
------------------------------------------------------------------------

setCourseHead : ∀ {A} → String → String → String → String → Cmd A
setCourseHead title description imageUrl canonicalUrl =
  setTitle title
    <> setDescription description
    <> setCanonical canonicalUrl
    <> setOgTitle title
    <> setOgDescription description
    <> setOgImage imageUrl
  where open Agdelte.Core.Cmd using (_<>_)
