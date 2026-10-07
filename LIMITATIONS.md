# Limitations

This repository proves the exact, finite and algebraic parts of *What Transport Keeps*. The
following parts of the paper are **not** formalized here.

**Credited to others.** The arithmetic identification belongs to the Ramanujan Challenge
authors: the Meijer-G evaluation that produces the initial column `f`, and the target limits
themselves, are cited, not proved. In this repository `G` (Catalan's constant) and `log 2` are
free real variables, so every Catalan identity holds whatever their values; nothing here proves
anything about the numbers themselves.

**Proved only in part.**

- **Theorems 1 and 2 (projector selection).** Only the combining step is proved: the two
  variational bounds give `1 - Tr(Q_N Q) ≤ 2η/δ`. The variational bounds themselves, and the
  asymptotic statement, are not.
- **Readout bound.** Only the scalar core is proved:
  `|c(a+P)/(c(b+Q)) - K| ≤ |P - KQ|/(|b| - |Q|)` when `|Q| < |b|`. The Cauchy–Schwarz step that
  bounds `P` and `Q` from the selection error is not.
- **Proposition 8 (projective-line capacity).** Only the exact boundary values
  `sin²(π/2) = 1`, `sin²(π/4) = 1/2`, `sin²(π/6) = 1/4` are proved, not the capacity count.
- **Proposition 9.** The derivative of the projector is proved entry by entry; the metric value
  `1/4` is proved from those entries.
- **Proposition 4a, dual certificate.** Proved as the general weak-duality lemma: for any `C`,
  `b`, `y` with `y ᵥ* C = b`, every `c` with `C c = 0` has `b ⬝ c = 0`. No specific certificate
  is instantiated.
- **Proposition 7.** The stress identity `½‖uuᵀ - vvᵀ‖²_F = 1 - (u·v)²` for unit `u, v` and its
  product rule are proved. The identities `BBᵀ = uuᵀ` and `BᵀB = vvᵀ` named in the header of
  `WTK/Response.lean` are not stated as separate theorems.
- **Appendices A and B, certificates.** The cubic `q`, the curvature numerator `curvNum` and
  denominator `curvDen` (already reduced modulo `q`) and the limiting matrix `B₀` are entered as
  explicit polynomials and an explicit matrix. Lean proves the signs of `q` at `0, 1, 4, 40`, that
  `curvNum` and `curvDen` vanish at no root of `q` (Bézout certificates), and the characteristic
  polynomial of `B₀`. It does not prove that `q` is the characteristic polynomial at
  `(n, k) = (2, 0)`, that `curvNum` and `curvDen` are the reduced curvature, or that `B₀` is the
  limit; the step from the sign pattern to three real roots (intermediate value theorem) is not
  formalized.

**Not proved.**

- The rotating-line control.
- The rail integral `G = ½ ∫ t sech t dt` and its remainder bounds.
- The Theorem 6a expansion.
- All numerical experiments, figures and floating-point tables in the paper and its code
  package.

**What the Field identities mean.** They are identities of rational functions, proved where the
denominators `D(n)` and `E(k)` are nonzero (the proofs clear denominators exactly). They say
nothing about points where a denominator vanishes.
