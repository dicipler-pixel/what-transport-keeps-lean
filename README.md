<div align="center">

# What Transport Keeps — Lean proofs

**The exact algebra of *What Transport Keeps*: conserved pairings, the Catalan cancellation and its certificates, the reconstructed Catalan matrix field, and the stress, projector and boundary-response identities, checked by Lean.**

[![Lean proof check](https://github.com/dicipler-pixel/what-transport-keeps-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/what-transport-keeps-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.34.1-blue)
![Theorems](https://img.shields.io/badge/theorems-49-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
[![Paper DOI](https://img.shields.io/badge/paper-10.5281%2Fzenodo.22543487-blue)](https://doi.org/10.5281/zenodo.22543487)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)

Jeromie Beasley

</div>

---

Companion to the paper *What Transport Keeps: Projector selection, conserved pairings, and
spectral geometry after the Ramanujan Challenge*
([10.5281/zenodo.22543487](https://doi.org/10.5281/zenodo.22543487); all versions
[10.5281/zenodo.22543486](https://doi.org/10.5281/zenodo.22543486)).

## What is proved

| File | Theorems | Paper | What it does |
| :--- | :-: | :--- | :--- |
| [`WTK/Transport.lean`](WTK/Transport.lean) | 8 | §1–2, Theorems 1, 3, 4 | The pairing `ℓᵀx` is conserved under `x ↦ Ax`, `ℓ ↦ A⁻ᵀℓ` and under moving frames; the scalar readout-error bound; coboundary telescoping in any monoid; the combining step `1 − Tr(Q_N Q) ≤ 2η/δ`; tied growth with and without a selected line |
| [`WTK/Catalan.lean`](WTK/Catalan.lean) | 10 | §3, Proposition 4a | `det U₀ = −382493/5040`; `A U₀⁻ᵀ f = 450 (G, 1)`, with `log 2` cancelling; the rational row `w` with `wᵀJ = (1, 0, 0)`; the weak-duality lemma behind the dual certificate (for general `C`, `b`, `y`); the numerator limit |
| [`WTK/Field.lean`](WTK/Field.lean) | 16 | §4, Proposition 5, Appendices A–B | The column convention `T(n,0) M(n) = σ(n) I`; the plaquette `L(n+1,k) T(n,k) = T(n,k−1) L(n,k)`; the factored `det T`; `B₀`'s characteristic polynomial `(z−1)(z²−34z+1)`; sign changes of `q`; Bézout certificates that the given curvature numerator and denominator polynomials (reduced modulo `q` outside Lean) never vanish at a root of `q`; the antisymmetric sum rule |
| [`WTK/Response.lean`](WTK/Response.lean) | 15 | §5–7, Propositions 7–10 | Rank-one stress `1 − (u·v)²` and its product rule; the capacity boundaries `1, 1/2, 1/4`; fixed levels `±Δ/2` with a moving projector, metric `1/4` and transition strength `d² sin²ϑ`; boundary elimination and exterior sensitivity for general matrix blocks |
| | **49** | | |

`G` (Catalan's constant) and `log 2` are free real variables in these files, so the Catalan
identities hold whatever their values. What is not proved (including the parts credited to the
Ramanujan Challenge authors) is listed in [`LIMITATIONS.md`](LIMITATIONS.md).

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml) on GitHub:

1. **Build**: every module compiles against Lean v4.34.1 and Mathlib `v4.34.1`.
2. **Independent replay**: every module is re-checked by Lean's separate kernel checker.
3. **Axiom audit**: every named theorem depends only on `propext`, `Classical.choice` and
   `Quot.sound`. No `sorry`, no project axioms, no `native_decide`.
4. **False controls**: two deliberately wrong claims must fail to compile, for a mathematical
   reason: that the Catalan readout is `45 (G, 1)` (it is `450 (G, 1)`), and that the limiting
   roots `17 ± 12√2` multiply to `2` (they multiply to `1`).

```bash
lake exe cache get
lake build
python3 scripts/verify.py
```

## Licence, citation and AI use

Copyright (c) 2026 Jeromie Beasley. Code and proofs: [MIT](LICENSE). Written text:
[CC BY 4.0](LICENSE-CC-BY-4.0.md). See [`LICENSING.md`](LICENSING.md). Citation metadata is in
[`CITATION.cff`](CITATION.cff); where the files came from is in [`PROVENANCE.md`](PROVENANCE.md);
how AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
