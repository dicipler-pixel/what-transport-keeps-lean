import Mathlib

/-!
# Selection, pairing and bookkeeping (Sections 1 and 2)

* **Theorem 3 (dual conservation).** If `x ↦ A x` and `ℓ ↦ A⁻ᵀ ℓ`, the pairing `ℓᵀ x` is
  unchanged; it is also unchanged under a moving coordinate change `x' = S⁻¹ x`, `ℓ' = Sᵀ ℓ`.
* **Readout error.** With `K = a/b`, selection error `P, Q` and any common scalar `c`,
  `|c(a+P)/(c(b+Q)) - K| ≤ |P - K Q| / (|b| - |Q|)` whenever `|Q| < |b|`.
* **Theorem 4 (coboundary bookkeeping).** If `T(n) U(n+1) = U(n) C(n)` then
  `T(0)⋯T(N-1) U(N) = U(0) C(0)⋯C(N-1)`, in any monoid.
* **Theorem 1, the combining step.** The two variational bounds give `1 - Tr(Q_N Q) ≤ 2η/δ`.
* **Tied growth.** `B_N = 2ᴺ diag(2, 1)` has normalized Gram matrix `diag(4/5, 1/5)` for every
  `N` (a fixed top line); `B_N = 2ᴺ I` has a scalar Gram matrix (no selected line).
-/

open Matrix

namespace WTK.Transport

section Pairing

variable {n R : Type*} [Fintype n] [DecidableEq n] [Field R]

/-- Theorem 3: the pairing `ℓᵀx` is conserved by `x ↦ A x`, `ℓ ↦ A⁻ᵀ ℓ`. -/
theorem pairing_conserved (A : Matrix n n R) (hA : IsUnit A.det) (ℓ x : n → R) :
    ((A⁻¹)ᵀ *ᵥ ℓ) ⬝ᵥ (A *ᵥ x) = ℓ ⬝ᵥ x := by
  rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    Matrix.nonsing_inv_mul _ hA, Matrix.vecMul_one]

/-- Theorem 3: the pairing is unchanged by a coordinate change `x' = S⁻¹x`, `ℓ' = Sᵀℓ`. -/
theorem pairing_frame_invariant (S : Matrix n n R) (hS : IsUnit S.det) (ℓ x : n → R) :
    (Sᵀ *ᵥ ℓ) ⬝ᵥ (S⁻¹ *ᵥ x) = ℓ ⬝ᵥ x := by
  rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    Matrix.mul_nonsing_inv _ hS, Matrix.vecMul_one]

end Pairing

/-- The finite readout-error bound. `a = px`, `b = qx`, `P = pr`, `Q = qr`, `K = a/b`; the
common scalar `c` cancels. -/
theorem readout_error (a b P Q c : ℂ) (hb : b ≠ 0) (hc : c ≠ 0) (hQ : ‖Q‖ < ‖b‖) :
    ‖c * (a + P) / (c * (b + Q)) - a / b‖ ≤ ‖P - a / b * Q‖ / (‖b‖ - ‖Q‖) := by
  have hbQ : b + Q ≠ 0 := by
    intro h
    have hQb : Q = -b := by linear_combination h
    rw [hQb, norm_neg] at hQ
    exact lt_irrefl _ hQ
  have e : c * (a + P) / (c * (b + Q)) - a / b = (P - a / b * Q) / (b + Q) := by
    field_simp <;> ring
  have hlow : ‖b‖ - ‖Q‖ ≤ ‖b + Q‖ := by
    have := norm_sub_norm_le b (-Q)
    simpa [norm_neg, sub_neg_eq_add] using this
  rw [e, norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (by linarith) hlow

/-- Right-ordered product `f 0 * f 1 * ⋯ * f (N-1)`. -/
def rprod {M : Type*} [Monoid M] (f : ℕ → M) : ℕ → M
  | 0 => 1
  | N + 1 => rprod f N * f N

/-- Theorem 4: coboundary bookkeeping. If `T(n) U(n+1) = U(n) C(n)` for all `n`, then
`T(0)⋯T(N-1) U(N) = U(0) C(0)⋯C(N-1)`; both endpoint frames are present. -/
theorem coboundary_telescope {M : Type*} [Monoid M] (T U C : ℕ → M)
    (h : ∀ i, T i * U (i + 1) = U i * C i) (N : ℕ) :
    rprod T N * U N = U 0 * rprod C N := by
  induction N with
  | zero => simp [rprod]
  | succ N ih =>
    simp only [rprod]
    rw [mul_assoc, h N, ← mul_assoc, ih, mul_assoc]

/-- Theorem 1, combining step: from `v*Hv ≥ λ₁ - 2η` and `v*Hv ≤ λ₁ - δ(1 - |u*v|²)` with a
positive gap `δ`, the top projectors satisfy `1 - Tr(Q_N Q) = 1 - |u*v|² ≤ 2η/δ`. -/
theorem gram_selection_step (l₁ η δ s c : ℝ) (hδ : 0 < δ)
    (h1 : l₁ - 2 * η ≤ s) (h2 : s ≤ l₁ - δ * (1 - c)) : 1 - c ≤ 2 * η / δ := by
  rw [le_div_iff₀ hδ]
  linarith

/-- Tied growth, a selected line: `B_N = 2ᴺ diag(2, 1)` has Gram matrix `(2ᴺ)² diag(4, 1)`. -/
theorem tied_fixed_gram (N : ℕ) :
    ((2 : ℝ) ^ N • diagonal ![(2 : ℝ), 1])ᵀ * ((2 : ℝ) ^ N • diagonal ![(2 : ℝ), 1]) =
      ((2 : ℝ) ^ N) ^ 2 • diagonal ![(4 : ℝ), 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, diagonal] <;> ring

/-- Its trace-normalized Gram matrix is `diag(4/5, 1/5)` at every depth: the top line `e₁` is
fixed although both modes grow at the same exponential rate. -/
theorem tied_fixed_normalized (N : ℕ) :
    (1 / (((2 : ℝ) ^ N) ^ 2 * 5)) • (((2 : ℝ) ^ N) ^ 2 • diagonal ![(4 : ℝ), 1]) =
      diagonal ![(4 : ℝ) / 5, 1 / 5] := by
  have h : ((2 : ℝ) ^ N) ^ 2 ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal] <;> field_simp <;> ring

/-- Tied growth, an unresolved block: `B_N = 2ᴺ I` has scalar Gram matrix `(2ᴺ)² I`, so every
line is a top line and selecting one adds a convention. -/
theorem tied_block_gram (N : ℕ) :
    ((2 : ℝ) ^ N • (1 : Matrix (Fin 2) (Fin 2) ℝ))ᵀ * ((2 : ℝ) ^ N • 1) =
      ((2 : ℝ) ^ N) ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [Matrix.transpose_smul, Matrix.transpose_one, smul_mul_smul_comm, Matrix.one_mul, sq]

end WTK.Transport
