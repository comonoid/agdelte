# packs

Vertical packages (SPEC §4, §9): `psychology/`, `vet/`, `medical/`, `transfer/`.
Each configures the neutral `services-core` for a domain; depends **down** on
`services-core` and `agdelte`. Each pack becomes its own `.agda-lib` when added.
