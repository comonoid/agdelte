# Agdelte Documentation

## Guide

| Document | Description |
|----------|-------------|
| [Getting Started](guide/getting-started.md) | Prerequisites, build, run, project structure |
| [Architecture](guide/architecture.md) | Core architecture and design principles |
| [Examples](guide/examples.md) | Guide to all examples (browser + server) |

## API Reference

| Module | Description |
|--------|-------------|
| [Node](api/node.md) | ReactiveApp, Node, Attr, Binding, zoomNode, Lens |
| [Event](api/event.md) | Subscriptions: interval, keyboard, WebSocket, workers, parallel, race |
| [Cmd](api/cmd.md) | Commands: HTTP, DOM, clipboard, storage, routing, agent interaction |
| [Task](api/task.md) | Monadic chains: sequential HTTP, do-notation |
| [Optic](api/optic.md) | Lens, Prism, Affine, Traversal, Optic, ProcessOptic, RemoteOptic, BigLens |
| [Agent](api/agent.md) | Agent coalgebra, Wiring, SharedAgent, Diagram, Inspector |
| [Signal](api/signal.md) | Synchronous streams: const, map, delay/pre, fold |
| [Session](api/session.md) | Session types: send/recv, dual, offer/choose, protocol builders |
| [CSS](api/css.md) | Typed CSS DSL: Decl, Length, Color, Layout, Transitions, Animations, Stylesheet |
| [SVG](api/svg.md) | Typed SVG DSL: Elements, Attributes, Path, Transform, ViewBox, SMIL, Events |
| [Anim](api/anim.md) | Model-driven animations: Tween, Spring (gentle, snappy, bouncy) |
| [FFI](api/ffi.md) | Browser/Server postulates, Serialize, Testing |

## Theory

| Document | Description |
|----------|-------------|
| [Polynomials](theory/polynomials.md) | Polynomial functors: theory and role in the project |
| [Combinators](theory/combinators.md) | All combinators with types and examples |
| [Time Model](theory/time-model.md) | Time model: ticks, dt |

## Internals

| Document | Description |
|----------|-------------|
| [Runtime](internals/runtime.md) | JavaScript runtime implementation |

## Comparison

| Document | Description |
|----------|-------------|
| [vs Svelte](comparison/vs-svelte.md) | Detailed comparison with Svelte 5 |
| [vs Vue 3](comparison/vs-vue3.md) | Feature comparison with Vue 3 |

## Project Status

| Document | Description |
|----------|-------------|
| [TODO](TODO.md) | Future improvements and nice-to-haves |

## Quick Links

- [Main README](../README.md) — project overview
- [Examples](../examples/) — browser examples (Agda source)
- [Server](../server/) — server examples (Agda source)
- [Theory](../src/Agdelte/Theory/) — formal foundations
