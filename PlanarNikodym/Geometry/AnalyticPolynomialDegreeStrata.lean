import PlanarNikodym.Geometry.AnalyticPolynomialDivision

/-! Actual finite degree strata and analytic monic normalization on their
nonvanishing coefficient neighborhoods. Degree jumps are retained as explicit
coefficient equations, not suppressed by an analyticity assertion. -/
noncomputable section
open Set Filter Polynomial
open scoped Topology
namespace PlanarNikodym

/-- An exact degree stratum, expressed in the original coefficients. -/
def polynomialDegreeStratum {E : Type*} (p : E → ℝ[X]) (d : ℕ) : Set E :=
  {x | (p x).coeff d ≠ 0 ∧ ∀ k, d < k → (p x).coeff k = 0}

theorem mem_polynomialDegreeStratum_iff {E : Type*} (p : E → ℝ[X]) (d : ℕ) (x : E) :
    x ∈ polynomialDegreeStratum p d ↔ p x ≠ 0 ∧ (p x).natDegree = d := by
  constructor
  · intro hx
    have hn : p x ≠ 0 := by intro h; exact hx.1 (by simp [h])
    refine ⟨hn, le_antisymm ?_ (le_natDegree_of_ne_zero hx.1)⟩
    exact natDegree_le_iff_coeff_eq_zero.mpr hx.2
  · rintro ⟨hn, hd⟩
    refine ⟨?_, fun k hk => coeff_eq_zero_of_natDegree_lt (hd ▸ hk)⟩
    rw [← hd, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hn

/-- A uniform coefficient bound gives a finite disjoint degree split, plus the
actual zero polynomial stratum. No degree is selected continuously across a jump. -/
theorem polynomial_finite_degree_split {E : Type*} (p : E → ℝ[X]) (N : ℕ)
    (hb : ∀ x k, N ≤ k → (p x).coeff k = 0) :
    (∀ x, p x = 0 ∨ ∃ d : Fin N, x ∈ polynomialDegreeStratum p d) ∧
    Pairwise (fun i j : Fin N => Disjoint (polynomialDegreeStratum p i)
      (polynomialDegreeStratum p j)) := by
  classical
  constructor
  · intro x
    by_cases hz : p x = 0
    · exact Or.inl hz
    · right
      have hd : (p x).natDegree < N := by
        by_contra h
        have hzero := hb x (p x).natDegree (Nat.le_of_not_gt h)
        rw [coeff_natDegree, leadingCoeff_eq_zero] at hzero
        exact hz hzero
      exact ⟨⟨(p x).natDegree, hd⟩,
        (mem_polynomialDegreeStratum_iff p _ x).mpr ⟨hz, rfl⟩⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hi hj
    have hi' := (mem_polynomialDegreeStratum_iff p i x).mp hi
    have hj' := (mem_polynomialDegreeStratum_iff p j x).mp hj
    exact hij (Fin.ext (hi'.2.symm.trans hj'.2))

/-- Each stratum uses finitely many explicit original coefficient tests. -/
theorem polynomialDegreeStratum_eq_finite_tests {E : Type*} (p : E → ℝ[X])
    (N d : ℕ) (hb : ∀ x k, N ≤ k → (p x).coeff k = 0) :
    polynomialDegreeStratum p d =
      {x | (p x).coeff d ≠ 0 ∧ ∀ k ∈ Finset.range N, d < k → (p x).coeff k = 0} := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, fun k _ hk => hx.2 k hk⟩
  · rintro ⟨hn, hz⟩
    refine ⟨hn, ?_⟩
    intro k hk
    by_cases hN : k < N
    · exact hz k (Finset.mem_range.mpr hN) hk
    · exact hb x k (Nat.le_of_not_gt hN)

def polynomialMonicCoefficients {E : Type*} (p : E → ℝ[X]) (d : ℕ) (x : E) :
    Fin d → ℝ := fun i => (p x).coeff i / (p x).coeff d

/-- On the true degree stratum the normalized polynomial equals the original up
to its nonzero leading coefficient, so no root information is lost. -/
theorem polynomial_eq_leading_mul_monic_on_stratum {E : Type*}
    (p : E → ℝ[X]) (d : ℕ) (x : E) (hx : x ∈ polynomialDegreeStratum p d) :
    p x = C ((p x).coeff d) * weierstrassPolynomial (polynomialMonicCoefficients p d x) := by
  ext k
  rw [coeff_C_mul]
  by_cases hk : k < d
  · change (p x).coeff k = (p x).coeff d *
      (weierstrassPolynomial (polynomialMonicCoefficients p d x)).coeff (⟨k, hk⟩ : Fin d)
    rw [weierstrassPolynomial_coeff_lt]
    simp only [polynomialMonicCoefficients]
    field_simp [hx.1]
  · by_cases hkd : k = d
    · subst k
      have h := (weierstrassPolynomial_monic (polynomialMonicCoefficients p d x)).coeff_natDegree
      rw [weierstrassPolynomial_natDegree] at h
      rw [h, mul_one]
    · have hdk : d < k := by omega
      have hz : (weierstrassPolynomial (polynomialMonicCoefficients p d x)).coeff k = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [weierstrassPolynomial_natDegree]; exact hdk)
      rw [hx.2 k hdk, hz, mul_zero]

theorem polynomial_monic_normalization_roots_iff {E : Type*}
    (p : E → ℝ[X]) (d : ℕ) (x : E) (hx : x ∈ polynomialDegreeStratum p d) (t : ℝ) :
    (weierstrassPolynomial (polynomialMonicCoefficients p d x)).eval t = 0 ↔
      (p x).eval t = 0 := by
  conv_rhs => rw [polynomial_eq_leading_mul_monic_on_stratum p d x hx]
  simp only [eval_mul, eval_C, mul_eq_zero, hx.1, false_or]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem analyticAt_polynomialMonicCoefficients (p : E → ℝ[X]) (d : ℕ) (x₀ : E)
    (hp : ∀ k, AnalyticAt ℝ (fun x => (p x).coeff k) x₀)
    (hd : (p x₀).coeff d ≠ 0) :
    AnalyticAt ℝ (polynomialMonicCoefficients p d) x₀ := by
  apply analyticAt_pi_iff.mpr
  intro i
  exact (hp i).div (hp d) hd

/-- The normalization extends analytically to an actual open neighborhood,
while its equality with the original polynomial is asserted on the degree stratum.
All higher-coefficient equations remain explicit. -/
theorem exists_open_nhds_analytic_monic_normalization
    (p : E → ℝ[X]) (d : ℕ) (x₀ : E)
    (hp : ∀ k, AnalyticAt ℝ (fun x => (p x).coeff k) x₀)
    (hd : (p x₀).coeff d ≠ 0) :
    ∃ U : Set E, IsOpen U ∧ x₀ ∈ U ∧
      AnalyticOnNhd ℝ (polynomialMonicCoefficients p d) U ∧
      (∀ x ∈ U, (p x).coeff d ≠ 0) ∧
      ∀ x ∈ U ∩ polynomialDegreeStratum p d,
        p x = C ((p x).coeff d) *
          weierstrassPolynomial (polynomialMonicCoefficients p d x) := by
  have ha := analyticAt_polynomialMonicCoefficients p d x₀ hp hd
  have hev : {x | AnalyticAt ℝ (polynomialMonicCoefficients p d) x ∧
      (p x).coeff d ≠ 0} ∈ 𝓝 x₀ :=
    ha.eventually_analyticAt.and ((hp d).continuousAt.eventually_ne hd)
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hev
  exact ⟨U, hU, hxU, fun x hx => (hUsub hx).1,
    fun x hx => (hUsub hx).2, fun x hx =>
      polynomial_eq_leading_mul_monic_on_stratum p d x hx.2⟩

end PlanarNikodym
