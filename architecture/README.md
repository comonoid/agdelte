# Architecture Notes

> **Main documentation: [doc/](../doc/)**
>
> This directory contains design documents for Phase 7 (implemented) and beyond.

## Documents

| Document | Status | Description |
|----------|--------|-------------|
| [concurrency.md](concurrency.md) | Partial | Browser-side concurrency: Web Workers (basic worker ✅), pools/channels (planned) |
| [dual-backend.md](dual-backend.md) | ✅ Done | Dual-backend: JS (browser) + Haskell/MAlonzo (server). All sub-phases 7A–7D implemented. |

## Phase 7 Implementation Summary

| Sub-phase | What | Files |
|-----------|------|-------|
| 7A | Agent coalgebra (pure, both backends) | `src/Agdelte/Concurrent/Agent.agda` |
| 7B | Web Worker runtime (browser) | `examples/Worker.agda`, `runtime/events.js` |
| 7C | Haskell HTTP server + RemoteAgent | `server/HttpAgent.agda`, `hs/Agdelte/Http.hs`, `examples/RemoteAgent.agda` |
| 7D | Multi-Agent + WebSocket broadcast | `server/MultiAgent.agda`, `hs/Agdelte/AgentServer.hs`, `hs/Agdelte/WebSocket.hs` |
| 7+ | Cmd agent combinators, Live Dashboard | `src/Agdelte/Core/Cmd.agda`, `examples_html/live-agent.html` |

## Completed Phase Documentation (in doc/)

| Document | Description |
|----------|-------------|
| [polynomials.md](../doc/polynomials.md) | Polynomial functors: theory and phase planning |
| [combinators.md](../doc/combinators.md) | All combinators with types and examples |
| [time-model.md](../doc/time-model.md) | Time model: ticks, dt |
| [vs-svelte.md](../doc/vs-svelte.md) | Detailed comparison with Svelte 5 |
| [vs-vue3.md](../doc/vs-vue3.md) | Feature comparison with Vue 3 |
