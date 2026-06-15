{-# OPTIONS --without-K #-}

-- Root module of the services-core layer (SPEC §4): neutral service machinery
-- reused across verticals — party/subject/engagement/resource/offering, money,
-- outbox, headless API, ACL. Depends DOWN on the agdelte framework only.
--
-- This placeholder proves the layer wiring (services-core builds against the
-- agdelte layer). Domain modules land here next (SPEC §14.4+).
module ServicesCore where

open import Agdelte.Json using (JsonValue)

-- re-exported so downstream modules have the agdelte JSON carrier in scope
open import Agdelte.Json public using (JsonValue)
