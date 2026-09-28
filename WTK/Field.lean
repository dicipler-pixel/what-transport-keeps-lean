import Mathlib

/-!
# The reconstructed Catalan matrix field (Proposition 5, Appendix A)

`Tm n k` is the column-transport matrix `T(n, k)` of the two-parameter Meijer-G field
reconstructed in Section 4, `Lm n k` the `n`-step `L(n, k)`, and `Mm n` the official
Question 5 polynomial matrix `M(n)`. The entries are exactly those of `cmf_explicit.py` in the
paper's code package, with each denominator written in factored form.

Proved here, as identities of rational functions on the domain where the denominators are
nonzero:

* `T(n, 0) M(n) = σ(n) I` with `σ(n) = -2 (n+2)² (n+3)² (2n+5) (2n+7)²`;
* the plaquette identity `L(n+1, k) T(n, k) = T(n, k-1) L(n, k)`;
* `det T = (2n+7)(k-n-3)(k-n-2)(2k-2n-7)(2k-2n-5) / ((n+1)(n+2)(2n+3)²(2n+5))`.

And the finite certificates of Appendix A and B: the limiting matrix `B₀` has characteristic
polynomial `(z - 1)(z² - 34z + 1)`; the cubic `q` at `(n, k) = (2, 0)` changes sign on
`(0, 1)`, `(1, 4)`, `(4, 40)`; and explicit Bézout certificates show the curvature numerator
and denominator never vanish at a root of `q`. Finally the sum rule `Σ_b F_b = 0` for any
antisymmetric pair sum.
-/

open Matrix

namespace WTK.Field

def Tm (n k : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(36*k^2*n^2 + 152*k^2*n + 156*k^2 - 104*k*n^3 - 668*k*n^2 - 1420*k*n - 996*k + 68*n^4 + 580*n^3 + 1848*n^2 + 2604*n + 1368) / ((n + 1)*(n + 3)*(2*n + 3)*(2*n + 5)), (8*k^2*n^2 + 28*k^2*n + 20*k^2 - 72*k*n^3 - 412*k*n^2 - 784*k*n - 504*k + 96*n^4 + 780*n^3 + 2384*n^2 + 3273*n + 1723) / ((n + 1)*(n + 2)*(n + 3)*(2*n + 3)*(2*n + 5)), (-28*k^2*n - 68*k^2 + 48*k*n^2 + 304*k*n + 456*k - 120*n^2 - 585*n - 715) / ((n + 1)*(n + 2)*(n + 3)*(2*n + 3)*(2*n + 5));
    (14*k^2*n + 24*k^2 - 38*k*n^2 - 153*k*n - 150*k + 24*n^3 + 149*n^2 + 304*n + 204) / ((n + 1)*(2*n + 3)), (8*k^2*n + 8*k^2 - 56*k*n^2 - 188*k*n - 162*k + 68*n^3 + 398*n^2 + 778*n + 523) / (2*(n + 1)*(n + 2)*(2*n + 3)), (-20*k^2 + 32*k*n + 132*k - 80*n - 205) / (2*(n + 1)*(n + 2)*(2*n + 3));
    (20*k^2*n^2 + 98*k^2*n + 108*k^2 - 52*k*n^3 - 380*k*n^2 - 889*k*n - 666*k + 32*n^4 + 306*n^3 + 1069*n^2 + 1620*n + 900) / (2*(n + 1)*(2*n + 3)), (16*k^2*n^2 + 64*k^2*n + 48*k^2 - 88*k*n^3 - 580*k*n^2 - 1200*k*n - 798*k + 96*n^4 + 884*n^3 + 2970*n^2 + 4360*n + 2403) / (4*(n + 1)*(n + 2)*(2*n + 3)), (-24*k^2*n - 84*k^2 + 32*k*n^2 + 272*k*n + 540*k + 8*n^3 - 44*n^2 - 478*n - 801) / (4*(n + 1)*(n + 2)*(2*n + 3))]

def Lm (n k : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(-k + n + 2), (1), (0);
    (0), (-k + n + 2), (1);
    (-2*k*n^3 - 11*k*n^2 - 20*k*n - 12*k + 2*n^4 + 15*n^3 + 42*n^2 + 52*n + 24) / (2*k - 7), (4*k*n^2 + 16*k*n + 16*k - 2*n^2 - 8*n - 5) / (2*(2*k - 7)), (-4*k^2 + 8*k*n + 28*k - 8*n^2 - 44*n - 67) / (2*(2*k - 7))]

def Mm (n : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(-272*n^7 - 5160*n^6 - 41832*n^5 - 187890*n^4 - 505033*n^3 - 812505*n^2 - 724563*n - 276345), (384*n^6 + 6384*n^5 + 44168*n^4 + 162698*n^3 + 336377*n^2 + 369933*n + 169011), (-480*n^4 - 4980*n^3 - 19210*n^2 - 32690*n - 20730);
    (192*n^8 + 3944*n^7 + 35272*n^6 + 179374*n^5 + 567338*n^4 + 1142826*n^3 + 1431798*n^2 + 1020096*n + 316440), (-272*n^7 - 4936*n^6 - 38212*n^5 - 163504*n^4 - 417425*n^3 - 635588*n^2 - 534276*n - 191232), (320*n^5 + 3820*n^4 + 18050*n^3 + 42240*n^2 + 49000*n + 22560);
    (-128*n^9 - 2808*n^8 - 27184*n^7 - 152386*n^6 - 544956*n^5 - 1288868*n^4 - 2015172*n^3 - 2007570*n^2 - 1155672*n - 292680), (192*n^8 + 3752*n^7 + 31820*n^6 + 152852*n^5 + 454528*n^4 + 856111*n^3 + 996616*n^2 + 655020*n + 185904), (-16*n^7 - 472*n^6 - 4608*n^5 - 22164*n^4 - 59438*n^3 - 90792*n^2 - 73976*n - 24960)]

/-- `σ(n) = -2 (n+2)² (n+3)² (2n+5) (2n+7)²`. -/
def sigma (n : ℝ) : ℝ := -2 * (n + 2) ^ 2 * (n + 3) ^ 2 * (2 * n + 5) * (2 * n + 7) ^ 2

set_option maxHeartbeats 8000000 in
/-- Proposition 5: the column convention matches the official matrix, `T(n,0) M(n) = σ(n) I`. -/
theorem column_convention (n : ℝ) (h1 : n + 1 ≠ 0) (h2 : n + 2 ≠ 0) (h3 : n + 3 ≠ 0) (h4 : 2 * n + 3 ≠ 0) (h5 : 2 * n + 5 ≠ 0) :
    Tm n 0 * Mm n = sigma n • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Tm, Mm, sigma, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;>
    field_simp <;> ring

set_option maxHeartbeats 8000000 in
/-- Proposition 5: the global plaquette identity `L(n+1, k) T(n, k) = T(n, k-1) L(n, k)`. -/
theorem plaquette (n k : ℝ) (h1 : n + 1 ≠ 0) (h2 : n + 2 ≠ 0) (h3 : n + 3 ≠ 0) (h4 : 2 * n + 3 ≠ 0) (h5 : 2 * n + 5 ≠ 0) (h7 : 2 * k - 7 ≠ 0) :
    Lm (n + 1) k * Tm n k = Tm n (k - 1) * Lm n k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Tm, Lm, Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp <;> ring

set_option maxHeartbeats 8000000 in
/-- Proposition 5: the determinant of `T(n, k)`. -/
theorem det_T (n k : ℝ) (h1 : n + 1 ≠ 0) (h2 : n + 2 ≠ 0) (h3 : n + 3 ≠ 0) (h4 : 2 * n + 3 ≠ 0) (h5 : 2 * n + 5 ≠ 0) :
    (Tm n k).det = (2 * n + 7) * (k - n - 3) * (k - n - 2) * (2 * k - 2 * n - 7) *
      (2 * k - 2 * n - 5) / ((n + 1) * (n + 2) * (2 * n + 3) ^ 2 * (2 * n + 5)) := by
  rw [Matrix.det_fin_three]
  simp [Tm] <;> field_simp <;> ring

/-- Appendix B: the limiting matrix `B₀`. -/
def B0 : Matrix (Fin 3) (Fin 3) ℝ := !![17, 24, 0; 12, 17, 0; 8, 12, 1]

/-- `det(z I - B₀) = (z - 1)(z² - 34 z + 1)`: the limiting eigenvalues are `1` and
`17 ± 12√2`, all simple. -/
theorem B0_charpoly (z : ℝ) :
    (z • (1 : Matrix (Fin 3) (Fin 3) ℝ) - B0).det = (z - 1) * (z ^ 2 - 34 * z + 1) := by
  rw [Matrix.det_fin_three]
  simp [B0, Matrix.one_apply] <;> ring

/-- `17 + 12√2` is a root of `z² - 34 z + 1`. -/
theorem rail_root : (17 + 12 * Real.sqrt 2) ^ 2 - 34 * (17 + 12 * Real.sqrt 2) + 1 = 0 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  linear_combination 144 * h

/-- The two nontrivial roots multiply to one: `(17 + 12√2)(17 - 12√2) = 1`. -/
theorem rail_roots_product : (17 + 12 * Real.sqrt 2) * (17 - 12 * Real.sqrt 2) = 1 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  linear_combination -144 * h

/-- In the rail parametrization `sec ψ = 17`, `tan ψ = 12√2` satisfy `sec² ψ - tan² ψ = 1`. -/
theorem rail_secant : (17 : ℝ) ^ 2 - (12 * Real.sqrt 2) ^ 2 = 1 := by
  rw [mul_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- The cubic of Appendix A (the characteristic polynomial at `(n, k) = (2, 0)`, scaled). -/
def q (z : ℝ) : ℝ := 211680 * z ^ 3 - 8545334 * z ^ 2 + 26602699 * z - 871200

/-- Appendix A: the signs of `q` at `0, 1, 4, 40` are `-, +, -, +`, so its three roots are
real, simple, and lie in `(0,1)`, `(1,4)`, `(4,40)`. -/
theorem q_signs : q 0 < 0 ∧ 0 < q 1 ∧ q 4 < 0 ∧ 0 < q 40 := by
  norm_num [q]

/-- Curvature numerator of Appendix A (reduced modulo `q`). -/
def curvNum (z : ℝ) : ℝ :=
  -315692356934422501517904 * z ^ 2 + 971776779958348659730344 * z +
    148197892949119993795200

/-- Curvature denominator of Appendix A (reduced modulo `q`). -/
def curvDen (z : ℝ) : ℝ :=
  8036886764505094218878498 * z ^ 2 - 32312696044376681193609433 * z +
    10593126561603564973615860

/-- Bézout certificate for `gcd(a, q) = 1`. -/
theorem bezout_num (z : ℝ) :
    (8486174089031313664577391307051829218482235511520 * z ^ 2 -
        326418150648016427807953315953003997920923126660726 * z +
        467811845948545494997923713089217811842385487989031) * curvNum z +
      (12655991588823323833779717938551898835140845310019985031341441855056 * z -
        14855947784233519125658110374280904213688368411944010749936746772936) * q z =
      82271231575837001011066742885602678598980826731717570928512520634242294400 := by
  unfold curvNum q
  ring

/-- Bézout certificate for `gcd(b, q) = 1`. -/
theorem bezout_den (z : ℝ) :
    (4959907260380286717936444480 * z ^ 2 - 190256285637138620595493435684 * z +
        254371183808741559784424914477) * curvDen z +
      (378561922980360148226764060346587610544871565119 -
        188313553543665194696239531110044968062451564828 * z) * q z =
      2364782996410433136645962320238230883625981634419132420 := by
  unfold curvDen q
  ring

/-- Theorem 6 at `(2, 0)`: at every eigenvalue (every root of `q`) the curvature numerator and
denominator are both nonzero, so the eigenline curvature is defined and nonzero on all three
bands. -/
theorem curvature_nonzero (z : ℝ) (hz : q z = 0) : curvNum z ≠ 0 ∧ curvDen z ≠ 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have e := bezout_num z
    rw [h, hz] at e
    norm_num at e
  · have e := bezout_den z
    rw [h, hz] at e
    norm_num at e

/-- An antisymmetric double sum vanishes. -/
theorem antisymmetric_double_sum {ι : Type*} (s : Finset ι) (g : ι → ι → ℝ)
    (hg : ∀ b c, g b c = -g c b) : ∑ b ∈ s, ∑ c ∈ s, g b c = 0 := by
  have h : ∑ b ∈ s, ∑ c ∈ s, g b c = ∑ b ∈ s, ∑ c ∈ s, -g c b :=
    Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => hg b c))
  have h2 : ∑ b ∈ s, ∑ c ∈ s, -g c b = -∑ b ∈ s, ∑ c ∈ s, g b c := by
    rw [Finset.sum_comm]
    simp [Finset.sum_neg_distrib]
  linarith

/-- Theorem 6, sum rule: if the pair numerators are antisymmetric, `N_bc = -N_cb`, and the gaps
satisfy `d_bc² = d_cb²`, the band curvatures `F_b = Σ_c N_bc / d_bc²` sum to zero. -/
theorem curvature_sum_rule {ι : Type*} (s : Finset ι) (N d : ι → ι → ℝ)
    (hN : ∀ b c, N b c = -N c b) (hd : ∀ b c, d b c ^ 2 = d c b ^ 2) :
    ∑ b ∈ s, ∑ c ∈ s, N b c / d b c ^ 2 = 0 :=
  antisymmetric_double_sum s _ (fun b c => by rw [hN b c, hd b c]; ring)

end WTK.Field
