import Mathlib

/-!
# Catalan: the exact calibration anchor (Section 3)

`A` is the official `2 × 3` readout of Question 5, `U₀` the initial Krylov matrix, and
`f = J (G, log 2, 1)ᵀ` the initial column (scaled by `1/√π`). `G` and `log 2` are kept as
independent real variables, so every identity here holds whatever their values:

* `U₀` is invertible (`det U₀ = -382493/5040`), and `A U₀⁻ᵀ f = 450 (G, 1)`: the `log 2`
  coefficients cancel in both rows and the rational terms cancel in the first;
* Proposition 4a: the explicit rational row `w` satisfies `wᵀ J = (1, 0, 0)`, retaining the
  Catalan component while cancelling `log 2` and the constant; and the dual certificate
  (`Cᵀ y = bᵀ` forces `b c = 0` for every kernel vector `c`) excludes retention exactly;
* the numerator limit: `(z v - u) c ≡ 0` in `z` iff `u c = v c = 0`.

The Meijer-G evaluation that produces `f` and the limit itself are the challenge authors'
results and are not formalized.
-/

open Matrix

namespace WTK.Catalan

/-- The official readout matrix `A`. -/
def A : Matrix (Fin 2) (Fin 3) ℝ := !![30921, -32972, 8240; 33750, -36000, 9000]

/-- The initial Krylov matrix `U₀`. -/
noncomputable def U0 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 152 / 5, 195477 / 175; 0, 1723 / 90, 1963751 / 2800; 0, -143 / 18, -165201 / 560]

/-- The initial column `f`, with `G` and `L = log 2` as variables. -/
noncomputable def f (G L : ℝ) : Fin 3 → ℝ :=
  ![150 * G - 128 * L - 146 / 3, 24745 / 4 * G - 14624 / 3 * L - 823511 / 360,
    7225281 / 32 * G - 886784 / 5 * L - 2818419551 / 33600]

/-- The solution `v = U₀⁻ᵀ f`, written out. -/
noncomputable def v (G L : ℝ) : Fin 3 → ℝ :=
  ![150 * G - 128 * L - 146 / 3, 225 * G - 224 * L - 305 / 6, 675 / 2 * G - 416 * L - 1247 / 60]

theorem U0_det : U0.det = -382493 / 5040 := by
  rw [Matrix.det_fin_three]
  norm_num [U0]

/-- `U₀ᵀ v = f`. -/
theorem U0T_v (G L : ℝ) : U0ᵀ *ᵥ v G L = f G L := by
  ext i
  fin_cases i <;>
    simp [U0, v, f, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply] <;>
    ring

/-- `A v = 450 (G, 1)`. -/
theorem A_v (G L : ℝ) : A *ᵥ v G L = ![450 * G, 450] := by
  ext i
  fin_cases i <;> simp [A, v, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- The exact Catalan cancellation: `A U₀⁻ᵀ f = 450 (G, 1)`, for every value of `G` and `log 2`. -/
theorem catalan_cancellation (G L : ℝ) : A *ᵥ ((U0ᵀ)⁻¹ *ᵥ f G L) = ![450 * G, 450] := by
  have hdet : IsUnit (U0ᵀ).det := by
    rw [Matrix.det_transpose, U0_det]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  rw [← U0T_v, Matrix.mulVec_mulVec (v G L) (U0ᵀ)⁻¹ U0ᵀ, Matrix.nonsing_inv_mul _ hdet,
    Matrix.one_mulVec, A_v]

/-- The coefficient matrix `J` with `f = J (G, log 2, 1)ᵀ`. -/
noncomputable def J : Matrix (Fin 3) (Fin 3) ℝ :=
  !![150, -128, -146 / 3; 24745 / 4, -14624 / 3, -823511 / 360;
    7225281 / 32, -886784 / 5, -2818419551 / 33600]

/-- `f = J (G, log 2, 1)ᵀ`. -/
theorem f_eq_J (G L : ℝ) : f G L = J *ᵥ ![G, L, 1] := by
  ext i
  fin_cases i <;> simp [f, J, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- The kernel-and-output witness of Proposition 4a. -/
noncomputable def w : Fin 3 → ℝ := ![2006814443 / 11474790, -1105372862 / 9562325, 5834864 / 1912465]

/-- Proposition 4a on the Catalan column: `wᵀ J = (1, 0, 0)`, so `w ⬝ f = G` exactly — the
`log 2` and constant components cancel while the Catalan component survives. -/
theorem w_certificate : w ᵥ* J = ![1, 0, 0] := by
  ext i
  fin_cases i <;> simp [w, J, Matrix.vecMul, dotProduct, Fin.sum_univ_three] <;> norm_num

/-- Consequently `w ⬝ f = G` for every value of `log 2`. -/
theorem w_reads_G (G L : ℝ) : w ⬝ᵥ f G L = G := by
  rw [f_eq_J, Matrix.dotProduct_mulVec, w_certificate]
  simp [dotProduct, Fin.sum_univ_three]

/-- Proposition 4a, dual certificate: if `Cᵀ y = bᵀ` then `b c = 0` for every `c` with
`C c = 0`, so no kernel vector retains the readout `b`. -/
theorem dual_certificate {m k R : Type*} [Fintype m] [Fintype k] [CommRing R]
    (C : Matrix m k R) (b : k → R) (y : m → R) (hy : y ᵥ* C = b) (c : k → R)
    (hc : C *ᵥ c = 0) : b ⬝ᵥ c = 0 := by
  rw [← hy, ← Matrix.dotProduct_mulVec, hc, dotProduct_zero]

/-- The two alternatives exclude each other: a retaining kernel vector rules out a dual
certificate. -/
theorem retention_excludes_certificate {m k R : Type*} [Fintype m] [Fintype k] [CommRing R]
    (C : Matrix m k R) (b : k → R) (c : k → R) (hc : C *ᵥ c = 0) (hbc : b ⬝ᵥ c ≠ 0) :
    ¬ ∃ y : m → R, y ᵥ* C = b := by
  rintro ⟨y, hy⟩
  exact hbc (dual_certificate C b y hy c hc)

/-- The numerator limit: `(z v - u) c` vanishes for every `z` iff `u c = v c = 0`, so
cancelling the whole formal error numerator also destroys the denominator. -/
theorem formal_numerator (uc vc : ℝ) : (∀ z : ℝ, z * vc - uc = 0) ↔ uc = 0 ∧ vc = 0 := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    constructor <;> linarith
  · rintro ⟨h1, h2⟩ z
    rw [h1, h2]
    ring

end WTK.Catalan
