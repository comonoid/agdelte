## Formal Proofs

From simple to complex:

- `dual (dual s) ≡ s` — session type involution proof (induction on `Session`, straightforward)
- Lens laws proofs (get-set, set-get, set-set) — for `fstLens`, `sndLens`, `idLens`, `_∘L_`
- `Agent ↔ Coalg P` correspondence — Agent IS a coalgebra of `p(y) = O × (I → y)`, mostly definitional
- `ReactiveApp ↔ Coalg` correspondence — App as coalgebra of `y^Msg`
- `Optic ≅ Poly.Lens` for monomial case — formal connection between practical optics and polynomial lenses
- `Big Lens ↔ Poly.Lens` — network-wide optic as polynomial lens (requires IOOptic formalization)
