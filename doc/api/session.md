# Session Types

From `Agdelte.Concurrent.Session` — typed communication protocols as sugar over polynomial lenses.

## Session

```agda
data Session : Set₁ where
  send   : (A : Set) → Session → Session   -- produce A, continue
  recv   : (A : Set) → Session → Session   -- consume A, continue
  offer  : Session → Session → Session      -- client picks branch (&)
  choose : Session → Session → Session      -- system picks branch (⊕)
  done   : Session                           -- protocol complete
```

## Duality

```agda
dual : Session → Session
-- send ↔ recv, offer ↔ choose, done ↔ done
```

## Interpretation

```agda
SessionI : Session → Set    -- input type for a session
SessionO : Session → Set    -- output type for a session
SessionAgent : Session → Set → Set
SessionAgent s S = Agent S (SessionI s) (SessionO s)
```

## Example Protocols

```agda
ReqResp : Set → Set → Session
ReqResp Req Resp = recv Req (send Resp done)

ProcessProtocol : Session
ProcessProtocol = offer
  (recv ⊤ (send String done))       -- peek
  (recv String (send String done))   -- step
```

## Smart Constructors

| Function | Type | Description |
|----------|------|-------------|
| `reqInput` | `Req → SessionI (ReqResp Req Resp)` | Pack request |
| `respOutput` | `SessionO (ReqResp Req Resp) → Resp` | Unpack response |
| `offerLeft` | `SessionI s₁ → SessionI (offer s₁ s₂)` | Select left branch |
| `offerRight` | `SessionI s₂ → SessionI (offer s₁ s₂)` | Select right branch |
| `peekLens` | `AgentLens ... (SessionI PeekProtocol) (SessionO PeekProtocol)` | Lens for peek |
| `stepLens` | `AgentLens ... (SessionI StepProtocol) (SessionO StepProtocol)` | Lens for step |

## Builders

```agda
mkReqResp : S → (S → Resp) → (S → Req → S) → SessionAgent (ReqResp Req Resp) S
mkOffer : SessionAgent s₁ S₁ → SessionAgent s₂ S₂ → SessionAgent (offer s₁ s₂) (S₁ × S₂)
```
