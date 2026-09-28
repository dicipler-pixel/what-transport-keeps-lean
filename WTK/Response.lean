import Mathlib

/-!
# Stress, capacity and boundary response (Sections 5, 6 and 7)

* **Proposition 7.** For unit `u, v` and `B = u vᵀ`, `BBᵀ = uuᵀ`, `BᵀB = vvᵀ`, and the stress
  `½‖uuᵀ - vvᵀ‖²_F = 1 - (u·v)²`. The overlap of a tensor product is the product of overlaps,
  so `1 - S(B ⊗ C) = (1 - S(B))(1 - S(C))`.
* **Proposition 8, boundary values.** `sin²(π/2) = 1`, `sin²(π/4) = 1/2`, `sin²(π/6) = 1/4`,
  the exact boundaries at which the projective-line capacity is `2`, `4`, `6`.
* **Proposition 9.** For `H_ϑ = (Δ/2)(cos ϑ σ_z + sin ϑ σ_x)`: `H_ϑ² = (Δ/2)² I`, so the levels
  stay at `±Δ/2`; the lower projector is idempotent with trace one; the metric
  `½ Tr[(∂_ϑ P)²] = 1/4`; and the transition strength `Tr(P D²) - Tr(P D)² = d² sin² ϑ`.
* **Proposition 10.** Eliminating interior and exterior variables leaves
  `K_Σ = D_Σ - C A⁻¹ B - G E⁻¹ F`, and a change of the exterior block moves it by exactly
  `G E⁻¹ (E' - E) E'⁻¹ F`.
-/

open Matrix

namespace WTK.Response

/-! ### Proposition 7 -/

/-- Proposition 7: for unit vectors, `½ Σᵢⱼ (uᵢuⱼ - vᵢvⱼ)² = 1 - (u·v)²`. -/
theorem rank_one_stress {n : Type*} [Fintype n] (u v : n → ℝ)
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) :
    (1 / 2) * ∑ i, ∑ j, (u i * u j - v i * v j) ^ 2 = 1 - (u ⬝ᵥ v) ^ 2 := by
  have e : ∑ i, ∑ j, (u i * u j - v i * v j) ^ 2 =
      (u ⬝ᵥ u) * (u ⬝ᵥ u) - 2 * ((u ⬝ᵥ v) * (u ⬝ᵥ v)) + (v ⬝ᵥ v) * (v ⬝ᵥ v) := by
    simp only [dotProduct]
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum]
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [e, hu, hv]
  ring

/-- The overlap of a tensor product is the product of the overlaps. -/
theorem tensor_overlap {n m : Type*} [Fintype n] [Fintype m] (u v : n → ℝ) (u' v' : m → ℝ) :
    ∑ p : n × m, (u p.1 * u' p.2) * (v p.1 * v' p.2) = (u ⬝ᵥ v) * (u' ⬝ᵥ v') := by
  rw [Fintype.sum_prod_type, dotProduct, dotProduct, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

/-- Proposition 7, composition law: with `S = 1 - overlap²`, `1 - S(B ⊗ C) = (1 - S(B))(1 - S(C))`. -/
theorem stress_composition {n m : Type*} [Fintype n] [Fintype m] (u v : n → ℝ) (u' v' : m → ℝ) :
    1 - (1 - (∑ p : n × m, (u p.1 * u' p.2) * (v p.1 * v' p.2)) ^ 2) =
      (1 - (1 - (u ⬝ᵥ v) ^ 2)) * (1 - (1 - (u' ⬝ᵥ v') ^ 2)) := by
  rw [tensor_overlap]
  ring

/-! ### Proposition 8: exact capacity boundaries -/

theorem capacity_boundary_two : Real.sin (Real.pi / 2) ^ 2 = 1 := by
  rw [Real.sin_pi_div_two]; norm_num

theorem capacity_boundary_four : Real.sin (Real.pi / 4) ^ 2 = 1 / 2 := by
  rw [Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]; norm_num

theorem capacity_boundary_six : Real.sin (Real.pi / 6) ^ 2 = 1 / 4 := by
  rw [Real.sin_pi_div_six]; norm_num

/-! ### Proposition 9: fixed levels, changing optical loading -/

/-- `H_ϑ = (Δ/2)(cos ϑ σ_z + sin ϑ σ_x)`. -/
noncomputable def Hθ (Δ θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Δ / 2 * Real.cos θ, Δ / 2 * Real.sin θ; Δ / 2 * Real.sin θ, -(Δ / 2 * Real.cos θ)]

/-- The lower projector `P_ϑ = (I - H_ϑ/(Δ/2))/2`. -/
noncomputable def Pθ (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 - Real.cos θ) / 2, -Real.sin θ / 2; -Real.sin θ / 2, (1 + Real.cos θ) / 2]

/-- Its entrywise derivative `∂_ϑ P_ϑ`. -/
noncomputable def dPθ (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.sin θ / 2, -Real.cos θ / 2; -Real.cos θ / 2, -Real.sin θ / 2]

/-- The levels are fixed: `H_ϑ² = (Δ/2)² I` for every `ϑ`. -/
theorem levels_fixed (Δ θ : ℝ) :
    Hθ Δ θ * Hθ Δ θ = (Δ / 2) ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have h := Real.sin_sq_add_cos_sq θ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Hθ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    first | ring1 | linear_combination (Δ / 2) ^ 2 * h

/-- `P_ϑ` is the lower projector of `H_ϑ`: `P_ϑ = (I - H_ϑ/(Δ/2))/2`. -/
theorem P_from_H (Δ θ : ℝ) (hΔ : Δ ≠ 0) :
    Pθ θ = (1 / 2 : ℝ) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) - (2 / Δ) • Hθ Δ θ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pθ, Hθ, Matrix.one_apply] <;> field_simp <;> ring

/-- `P_ϑ` is idempotent. -/
theorem P_idempotent (θ : ℝ) : Pθ θ * Pθ θ = Pθ θ := by
  have h := Real.sin_sq_add_cos_sq θ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pθ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination (1 / 4 : ℝ) * h | linear_combination (-1 / 4 : ℝ) * h

/-- `P_ϑ` has trace one. -/
theorem P_trace (θ : ℝ) : (Pθ θ).trace = 1 := by
  rw [Matrix.trace_fin_two]
  simp [Pθ] <;> ring

/-- `dPθ` is the entrywise derivative of `Pθ`. -/
theorem P_hasDerivAt (θ : ℝ) (i j : Fin 2) :
    HasDerivAt (fun t => Pθ t i j) (dPθ θ i j) θ := by
  fin_cases i <;> fin_cases j <;> simp only [Pθ, dPθ]
  · simpa using ((Real.hasDerivAt_cos θ).const_sub 1).div_const 2
  · simpa [neg_div] using ((Real.hasDerivAt_sin θ).neg).div_const 2
  · simpa [neg_div] using ((Real.hasDerivAt_sin θ).neg).div_const 2
  · simpa using ((Real.hasDerivAt_cos θ).const_add 1).div_const 2

/-- Proposition 9, the metric: `g_ϑϑ = ½ Tr[(∂_ϑ P)²] = 1/4` for every `ϑ`. -/
theorem metric_quarter (θ : ℝ) : (1 / 2) * (dPθ θ * dPθ θ).trace = 1 / 4 := by
  have h := Real.sin_sq_add_cos_sq θ
  rw [Matrix.trace_fin_two]
  simp [dPθ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination (1 / 4 : ℝ) * h

/-- The dipole `D = d σ_z`. -/
def Dz (d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![d, 0; 0, -d]

/-- Proposition 9, the transition strength: the ground-state variance of `D`,
`Tr(P D²) - Tr(P D)²`, equals `d² sin² ϑ`. -/
theorem transition_strength (d θ : ℝ) :
    (Pθ θ * (Dz d * Dz d)).trace - ((Pθ θ * Dz d).trace) ^ 2 = d ^ 2 * Real.sin θ ^ 2 := by
  have h := Real.sin_sq_add_cos_sq θ
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp [Pθ, Dz, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination (-(d ^ 2)) * h

/-! ### Proposition 10: the interface retains loading from both sides -/

section Boundary

variable {ι β ο : Type*} [Fintype ι] [Fintype β] [Fintype ο]
  [DecidableEq ι] [DecidableEq β] [DecidableEq ο]

/-- The boundary operator `K_Σ = D_Σ - C A⁻¹ B - G E⁻¹ F`, with explicit inverses. -/
def boundaryOp (Ds : Matrix β β ℝ) (C : Matrix β ι ℝ) (Ai : Matrix ι ι ℝ) (B : Matrix ι β ℝ)
    (G : Matrix β ο ℝ) (Ei : Matrix ο ο ℝ) (F : Matrix ο β ℝ) : Matrix β β ℝ :=
  Ds - C * Ai * B - G * Ei * F

/-- Proposition 10: if the interior and exterior block equations hold, `A u_I + B u_Σ = 0` and
`F u_Σ + E u_O = 0`, the middle equation reads `C u_I + D_Σ u_Σ + G u_O = K_Σ u_Σ`. -/
theorem boundary_elimination (A Ai : Matrix ι ι ℝ) (B : Matrix ι β ℝ) (C : Matrix β ι ℝ)
    (Ds : Matrix β β ℝ) (G : Matrix β ο ℝ) (E Ei : Matrix ο ο ℝ) (F : Matrix ο β ℝ)
    (hA : Ai * A = 1) (hE : Ei * E = 1) (uI : ι → ℝ) (uS : β → ℝ) (uO : ο → ℝ)
    (h1 : A *ᵥ uI + B *ᵥ uS = 0) (h3 : F *ᵥ uS + E *ᵥ uO = 0) :
    C *ᵥ uI + Ds *ᵥ uS + G *ᵥ uO = boundaryOp Ds C Ai B G Ei F *ᵥ uS := by
  have hI : uI = -((Ai * B) *ᵥ uS) := by
    have := congrArg (fun x => Ai *ᵥ x) h1
    simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact eq_neg_of_add_eq_zero_left this
  have hO : uO = -((Ei * F) *ᵥ uS) := by
    have := congrArg (fun x => Ei *ᵥ x) h3
    simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, hE, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact eq_neg_of_add_eq_zero_right this
  rw [hI, hO, boundaryOp]
  simp only [Matrix.sub_mulVec, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  abel

/-- Proposition 10, exterior sensitivity (exact): replacing `E` by `E'` moves the boundary
operator by `G E⁻¹ (E' - E) E'⁻¹ F`; to first order this is `G E⁻¹ δE E⁻¹ F`. -/
theorem exterior_sensitivity (Ds : Matrix β β ℝ) (C : Matrix β ι ℝ) (Ai : Matrix ι ι ℝ)
    (B : Matrix ι β ℝ) (G : Matrix β ο ℝ) (E E' Ei Ei' : Matrix ο ο ℝ) (F : Matrix ο β ℝ)
    (hE : Ei * E = 1) (hE' : E' * Ei' = 1) :
    boundaryOp Ds C Ai B G Ei' F - boundaryOp Ds C Ai B G Ei F =
      G * (Ei * (E' - E) * Ei') * F := by
  have key : Ei * (E' - E) * Ei' = Ei - Ei' := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hE', Matrix.mul_one, hE,
      Matrix.one_mul]
  rw [key, boundaryOp, boundaryOp, Matrix.mul_sub, Matrix.sub_mul]
  simp only [Matrix.mul_assoc]
  abel

end Boundary

end WTK.Response
