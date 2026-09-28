import Mathlib

/-!
# The reconstructed Catalan matrix field (Proposition 5, Appendix A)

`Tm n k` is the column-transport matrix `T(n, k)` of the two-parameter Meijer-G field
reconstructed in Section 4, `Lm n k` the `n`-step `L(n, k)`, and `Mm n` the official
Question 5 polynomial matrix `M(n)`. `T` and `L` are written over their common denominators,
`T = Tnum / D(n)` and `L = Lnum / E(k)`, with `Tnum`, `Lnum` polynomial matrices; the entries
agree exactly with those of `cmf_explicit.py` in the paper's code package.

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

def Tnum (n k : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(144*k^2*n^3 + 896*k^2*n^2 + 1840*k^2*n + 1248*k^2 - 416*k*n^4 - 3504*k*n^3 - 11024*k*n^2 - 15344*k*n - 7968*k + 272*n^5 + 2864*n^4 + 12032*n^3 + 25200*n^2 + 26304*n + 10944), (32*k^2*n^2 + 112*k^2*n + 80*k^2 - 288*k*n^3 - 1648*k*n^2 - 3136*k*n - 2016*k + 384*n^4 + 3120*n^3 + 9536*n^2 + 13092*n + 6892), (-112*k^2*n - 272*k^2 + 192*k*n^2 + 1216*k*n + 1824*k - 480*n^2 - 2340*n - 2860);
    (112*k^2*n^4 + 1032*k^2*n^3 + 3512*k^2*n^2 + 5232*k^2*n + 2880*k^2 - 304*k*n^5 - 3504*k*n^4 - 16004*k*n^3 - 36204*k*n^2 - 40560*k*n - 18000*k + 192*n^6 + 2632*n^5 + 14924*n^4 + 44804*n^3 + 75112*n^2 + 66672*n + 24480), (32*k^2*n^3 + 208*k^2*n^2 + 416*k^2*n + 240*k^2 - 224*k*n^4 - 1984*k*n^3 - 6464*k*n^2 - 9204*k*n - 4860*k + 272*n^5 + 3088*n^4 + 13908*n^3 + 31148*n^2 + 34846*n + 15690), (-80*k^2*n^2 - 440*k^2*n - 600*k^2 + 128*k*n^3 + 1232*k*n^2 + 3864*k*n + 3960*k - 320*n^3 - 2580*n^2 - 6910*n - 6150);
    (80*k^2*n^5 + 992*k^2*n^4 + 4852*k^2*n^3 + 11692*k^2*n^2 + 13872*k^2*n + 6480*k^2 - 208*k*n^6 - 3080*k*n^5 - 18804*k*n^4 - 60574*k*n^3 - 108566*k*n^2 - 102624*k*n - 39960*k + 128*n^7 + 2184*n^6 + 15824*n^5 + 63114*n^4 + 149666*n^3 + 211020*n^2 + 163800*n + 54000), (32*k^2*n^4 + 304*k^2*n^3 + 1040*k^2*n^2 + 1488*k^2*n + 720*k^2 - 176*k*n^5 - 2128*k*n^4 - 10100*k*n^3 - 23496*k*n^2 - 26778*k*n - 11970*k + 192*n^6 + 2824*n^5 + 17104*n^4 + 54650*n^3 + 97316*n^2 + 91833*n + 36045), (-48*k^2*n^3 - 432*k^2*n^2 - 1284*k^2*n - 1260*k^2 + 64*k*n^4 + 896*k*n^3 + 4552*k*n^2 + 10020*k*n + 8100*k + 16*n^5 - 1320*n^3 - 7520*n^2 - 15981*n - 12015)]

def Lnum (n k : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(-4*k^2 + 4*k*n + 22*k - 14*n - 28), (4*k - 14), (0);
    (0), (-4*k^2 + 4*k*n + 22*k - 14*n - 28), (4*k - 14);
    (-4*k*n^3 - 22*k*n^2 - 40*k*n - 24*k + 4*n^4 + 30*n^3 + 84*n^2 + 104*n + 48), (4*k*n^2 + 16*k*n + 16*k - 2*n^2 - 8*n - 5), (-4*k^2 + 8*k*n + 28*k - 8*n^2 - 44*n - 67)]

def Mm (n : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(-272*n^7 - 5160*n^6 - 41832*n^5 - 187890*n^4 - 505033*n^3 - 812505*n^2 - 724563*n - 276345), (384*n^6 + 6384*n^5 + 44168*n^4 + 162698*n^3 + 336377*n^2 + 369933*n + 169011), (-480*n^4 - 4980*n^3 - 19210*n^2 - 32690*n - 20730);
    (192*n^8 + 3944*n^7 + 35272*n^6 + 179374*n^5 + 567338*n^4 + 1142826*n^3 + 1431798*n^2 + 1020096*n + 316440), (-272*n^7 - 4936*n^6 - 38212*n^5 - 163504*n^4 - 417425*n^3 - 635588*n^2 - 534276*n - 191232), (320*n^5 + 3820*n^4 + 18050*n^3 + 42240*n^2 + 49000*n + 22560);
    (-128*n^9 - 2808*n^8 - 27184*n^7 - 152386*n^6 - 544956*n^5 - 1288868*n^4 - 2015172*n^3 - 2007570*n^2 - 1155672*n - 292680), (192*n^8 + 3752*n^7 + 31820*n^6 + 152852*n^5 + 454528*n^4 + 856111*n^3 + 996616*n^2 + 655020*n + 185904), (-16*n^7 - 472*n^6 - 4608*n^5 - 22164*n^4 - 59438*n^3 - 90792*n^2 - 73976*n - 24960)]

/-- The common denominator `D(n) = 4 (n+1)(n+2)(n+3)(2n+3)(2n+5)` of `T`. -/
def Dn (n : ℝ) : ℝ := 4 * (n + 1) * (n + 2) * (n + 3) * (2 * n + 3) * (2 * n + 5)

/-- The denominator `E(k) = 2 (2k - 7)` of `L`. -/
def Ek (k : ℝ) : ℝ := 2 * (2 * k - 7)

/-- `T(n, k)`, written over its common denominator: `T = Tnum / D(n)`. -/
noncomputable def Tm (n k : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := (1 / Dn n) • Tnum n k

/-- `L(n, k)`, written over its common denominator: `L = Lnum / E(k)`. -/
noncomputable def Lm (n k : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := (1 / Ek k) • Lnum n k

/-- `σ(n) = -2 (n+2)² (n+3)² (2n+5) (2n+7)²`. -/
def sigma (n : ℝ) : ℝ := -2 * (n + 2) ^ 2 * (n + 3) ^ 2 * (2 * n + 5) * (2 * n + 7) ^ 2

/-- Cleared form of the column convention: `Tnum(n, 0) M(n) = D(n) σ(n) I`. -/
theorem column_convention_num (n : ℝ) :
    Tnum n 0 * Mm n = (Dn n * sigma n) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Tnum, Mm, Dn, sigma, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;> ring

/-- Proposition 5: the column convention matches the official matrix, `T(n,0) M(n) = σ(n) I`,
wherever the denominator `D(n)` is nonzero. -/
theorem column_convention (n : ℝ) (hD : Dn n ≠ 0) :
    Tm n 0 * Mm n = sigma n • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [Tm, smul_mul_assoc, column_convention_num, smul_smul]
  congr 1
  field_simp

/-- Cleared form of the plaquette identity: `Lnum(n+1, k) Tnum(n, k) = Tnum(n, k-1) Lnum(n, k)`. -/
theorem plaquette_num (n k : ℝ) :
    Lnum (n + 1) k * Tnum n k = Tnum n (k - 1) * Lnum n k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Tnum, Lnum, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- Proposition 5: the global plaquette identity `L(n+1, k) T(n, k) = T(n, k-1) L(n, k)`, as an
identity of rational functions (both sides carry the same denominators `D(n) E(k)`). -/
theorem plaquette (n k : ℝ) :
    Lm (n + 1) k * Tm n k = Tm n (k - 1) * Lm n k := by
  rw [Lm, Tm, Tm, Lm, smul_mul_smul_comm, smul_mul_smul_comm, plaquette_num, mul_comm (1 / Ek k)]

/-- Cleared form of the determinant:
`det Tnum = 64 (n+1)² (n+2)² (n+3)³ (2n+3) (2n+5)² (2n+7)(k-n-3)(k-n-2)(2k-2n-7)(2k-2n-5)`. -/
theorem det_num (n k : ℝ) :
    (Tnum n k).det = 64 * (n + 1) ^ 2 * (n + 2) ^ 2 * (n + 3) ^ 3 * (2 * n + 3) *
      (2 * n + 5) ^ 2 * (2 * n + 7) * (k - n - 3) * (k - n - 2) * (2 * k - 2 * n - 7) *
      (2 * k - 2 * n - 5) := by
  rw [Matrix.det_fin_three]
  simp [Tnum] <;> ring

/-- Proposition 5: `det T = (2n+7)(k-n-3)(k-n-2)(2k-2n-7)(2k-2n-5) / ((n+1)(n+2)(2n+3)²(2n+5))`. -/
theorem det_T (n k : ℝ) (h1 : n + 1 ≠ 0) (h2 : n + 2 ≠ 0) (h3 : n + 3 ≠ 0)
    (h4 : 2 * n + 3 ≠ 0) (h5 : 2 * n + 5 ≠ 0) :
    (Tm n k).det = (2 * n + 7) * (k - n - 3) * (k - n - 2) * (2 * k - 2 * n - 7) *
      (2 * k - 2 * n - 5) / ((n + 1) * (n + 2) * (2 * n + 3) ^ 2 * (2 * n + 5)) := by
  rw [Tm, Matrix.det_smul, det_num, Fintype.card_fin, Dn]
  field_simp <;> ring

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
