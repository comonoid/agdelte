{-# OPTIONS --without-K #-}

-- RemoteOptic: access agent state on a remote server via HTTP
--
-- Same peek/over conceptual interface as local Optic, but over HTTP.
-- Works from browser (JS backend) — uses Cmd for side effects.
--
-- Architecture:
--   Server: serveAgent on HTTP (Transport.hs / HttpAgent.agda)
--   Client: RemoteOptic wraps agentQuery/agentStep Cmd combinators
--
-- Protocol (over HTTP):
--   GET  {baseUrl}/state → current observation (String)
--   POST {baseUrl}/step  → step with body, return new observation
--
-- Uses Core/Cmd.agda for browser-side effects.
-- Uses FFI/Shared.agda Serialize for type-safe encoding/decoding.

module Agdelte.Reactive.RemoteOptic where

open import Data.String using (String; _++_)
open import Data.Maybe using (Maybe; just; nothing)

open import Agdelte.Core.Cmd as Cmd using (Cmd; httpGet; httpPost)
open import Agdelte.FFI.Shared using (Serialize; encode; decode; TransportResult; success; failure)

private
  variable
    A Msg : Set

------------------------------------------------------------------------
-- RemoteOptic: typed remote access over HTTP
------------------------------------------------------------------------

-- | A RemoteOptic connects to an agent on a remote server.
-- The baseUrl identifies the HTTP endpoint (e.g., "http://localhost:3000/counter").
-- Serialize instance provides type-safe encoding/decoding.
record RemoteOptic (A : Set) : Set where
  constructor mkRemoteOptic
  field
    baseUrl    : String
    {{serial}} : Serialize A

open RemoteOptic public

------------------------------------------------------------------------
-- Optic operations as Cmd (browser-side)
------------------------------------------------------------------------

-- | Peek: read remote agent state via HTTP GET
-- GET {baseUrl}/state → decode response → TransportResult A
queryRemote : RemoteOptic A
            → (TransportResult A → Msg) → (String → Msg)
            → Cmd Msg
queryRemote ro onResult onError =
  httpGet (baseUrl ro ++ "/state")
    (λ raw → onResult (decodeResult raw))
    onError
  where
    decodeResult : String → TransportResult _
    decodeResult raw with decode raw
    ... | just a  = success a
    ... | nothing = failure "decode failed"

-- | Step: modify remote agent state via HTTP POST
-- POST {baseUrl}/step with input → decode response → TransportResult A
stepRemote : RemoteOptic A
           → String
           → (TransportResult A → Msg) → (String → Msg)
           → Cmd Msg
stepRemote ro input onResult onError =
  httpPost (baseUrl ro ++ "/step") input
    (λ raw → onResult (decodeResult raw))
    onError
  where
    decodeResult : String → TransportResult _
    decodeResult raw with decode raw
    ... | just a  = success a
    ... | nothing = failure "decode failed"

------------------------------------------------------------------------
-- Simplified API (String-level, no Serialize required)
------------------------------------------------------------------------

-- | Query agent state (raw String, no decoding)
queryRemoteRaw : String
               → (String → Msg) → (String → Msg)
               → Cmd Msg
queryRemoteRaw url = httpGet (url ++ "/state")

-- | Step agent (raw String)
stepRemoteRaw : String → String
              → (String → Msg) → (String → Msg)
              → Cmd Msg
stepRemoteRaw url input = httpPost (url ++ "/step") input

------------------------------------------------------------------------
-- Event-based remote subscriptions
------------------------------------------------------------------------

-- For subscribing to remote agent changes, use:
--   Event.wsConnect url handler       — WebSocket for live updates
--   Event.httpGet (url ++ "/state")   — one-shot HTTP polling
--
-- RemoteOptic focuses on Cmd (imperative operations).
-- For reactive subscriptions, combine with Event primitives.
