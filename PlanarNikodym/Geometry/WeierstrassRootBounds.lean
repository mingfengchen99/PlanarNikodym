import PlanarNikodym.Geometry.WeierstrassPolynomial
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Continuity

/-! Uniform Cauchy bounds for the actual monic coefficient family. -/
noncomputable section
open Set Filter Polynomial
open scoped Topology NNReal
namespace PlanarNikodym

@[simp] theorem weierstrassPolynomial_coeff_lt {m : ℕ} (a : Fin m → ℝ)
    (i : Fin m) : (weierstrassPolynomial a).coeff i = a i := by
  classical
  simp only [weierstrassPolynomial, coeff_add, coeff_X_pow,
    if_neg (Nat.ne_of_lt i.is_lt), zero_add, finsetSum_coeff, coeff_C_mul_X_pow]
  have he (j : Fin m) : ((i : ℕ) = (j : ℕ)) ↔ i = j := Fin.val_inj
  simp_rw [he]
  simp

theorem weierstrassPolynomial_cauchyBound_le {m : ℕ} (a : Fin m → ℝ) :
    (weierstrassPolynomial a).cauchyBound ≤ ‖a‖₊ + 1 := by
  rw [cauchyBound, weierstrassPolynomial_natDegree,
    (weierstrassPolynomial_monic a).leadingCoeff, nnnorm_one, div_one]
  gcongr
  apply Finset.sup_le
  intro n hn
  have hn' : n < m := Finset.mem_range.mp hn
  change ‖(weierstrassPolynomial a).coeff (⟨n, hn'⟩ : Fin m)‖₊ ≤ ‖a‖₊
  rw [weierstrassPolynomial_coeff_lt]
  exact nnnorm_le_pi_nnnorm a ⟨n, hn'⟩

theorem abs_lt_norm_add_one_of_weierstrassPolynomial_root
    {m : ℕ} (a : Fin m → ℝ) {t : ℝ}
    (ht : (weierstrassPolynomial a).eval t = 0) : |t| < ‖a‖ + 1 := by
  have h := (show (weierstrassPolynomial a).IsRoot t from ht).norm_lt_cauchyBound
    (weierstrassPolynomial_monic a).ne_zero
  have h' := h.trans_le (weierstrassPolynomial_cauchyBound_le a)
  exact_mod_cast h'

/-- Near a continuous coefficient vector, every real root lies in one fixed
bounded interval. The bound also handles degree zero, whose polynomial has no roots. -/
theorem exists_open_nhds_uniform_weierstrass_root_bound
    {E : Type*} [TopologicalSpace E] {m : ℕ} (a : E → Fin m → ℝ) (x₀ : E)
    (ha : ContinuousAt a x₀) :
    ∃ (U : Set E) (R : ℝ), IsOpen U ∧ x₀ ∈ U ∧ 0 < R ∧
      ∀ x ∈ U, ∀ t : ℝ, (weierstrassPolynomial (a x)).eval t = 0 → |t| < R := by
  have hb : ∀ᶠ x in 𝓝 x₀, ‖a x‖ < ‖a x₀‖ + 1 :=
    ha.norm.eventually_lt continuousAt_const (lt_add_one _)
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hb
  refine ⟨U, ‖a x₀‖ + 2, hU, hxU, by positivity, ?_⟩
  intro x hx t ht
  have h := abs_lt_norm_add_one_of_weierstrassPolynomial_root (a x) ht
  have hb' : ‖a x‖ < ‖a x₀‖ + 1 := hUsub hx
  linarith

end PlanarNikodym
