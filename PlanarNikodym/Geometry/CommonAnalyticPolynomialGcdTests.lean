import PlanarNikodym.Geometry.CommonAnalyticPolynomialGcdStrata

/-! Literal finite analytic zero and nonzero tests on the original domain for
every branch of the constructed Euclidean gcd tree. -/
noncomputable section
open Set Filter Polynomial
open scoped Topology
namespace PlanarNikodym
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Clearing a finite family of denominators uses one finite family of
numerators analytic on the original domain. -/
theorem exists_common_analytic_fraction_zero_tests
    {U V : Set E} {n : ℕ} (t : E → Fin n → ℝ)
    (ht : ∀ i, AnalyticFractionOn U V (fun x => t x i)) :
    ∃ g : E → Fin n → ℝ, AnalyticOnNhd ℝ g U ∧
      ∀ x ∈ V, (∀ i, t x i = 0) ↔ ∀ i, g x i = 0 := by
  classical
  choose p hp he using fun i => (ht i).exists_common_analytic_zero_test
  refine ⟨fun x i => p i x, fun x hx => analyticAt_pi_iff.mpr (fun i => hp i x hx), ?_⟩
  intro x hx
  exact forall_congr' (fun i => (he i x hx).1)

/-- Every actual gcd carrier has a finite analytic description on the one
original domain, including all degree-drop and zero-remainder branches. -/
theorem CommonAnalyticPolynomialGcdStratification.exists_common_analytic_tests
    {U V : Set E} {P Q : E → ℝ[X]}
    (T : CommonAnalyticPolynomialGcdStratification U V P Q) (i : T.Index) :
    ∃ (n : ℕ) (f : E → Fin n → ℝ) (g : E → Fin (T.stratum i).testCount → ℝ),
      AnalyticOnNhd ℝ f U ∧ AnalyticOnNhd ℝ g U ∧
      ∀ x, x ∈ (T.stratum i).carrier ↔
        x ∈ U ∧ (∀ j, f x j ≠ 0) ∧ ∀ j, g x j = 0 := by
  obtain ⟨n, f, hf, he⟩ := T.ambient_common i
  obtain ⟨g, hg, hge⟩ := exists_common_analytic_fraction_zero_tests
    (T.stratum i).zeroTests (T.zero_test_fraction i)
  refine ⟨n, f, g, hf, hg, ?_⟩
  intro x
  rw [(T.valid i).2.2.2.2.1 x]
  constructor
  · rintro ⟨hx, hz⟩
    exact ⟨((he x).mp hx).1, ((he x).mp hx).2, (hge x hx).mp hz⟩
  · rintro ⟨hx, hn, hz⟩
    have hv := (he x).mpr ⟨hx, hn⟩
    exact ⟨hv, (hge x hv).mpr hz⟩

/-- The common-domain Euclidean construction starts directly from the original
analytic monic coefficient families. -/
theorem exists_common_analytic_polynomial_gcd_stratification
    {M N : ℕ} (a : E → Fin M → ℝ) (b : E → Fin N → ℝ)
    (U : Set E) (hU : IsOpen U)
    (ha : AnalyticOnNhd ℝ a U) (hb : AnalyticOnNhd ℝ b U) :
    Nonempty (CommonAnalyticPolynomialGcdStratification U U
      (fun x => weierstrassPolynomial (a x)) (fun x => weierstrassPolynomial (b x))) :=
  exists_common_analytic_fraction_gcd_stratification a b U U hU (CommonAnalyticOpen.self U)
    (fun i => AnalyticFractionOn.of_analytic (fun x hx => analyticAt_pi_iff.mp (ha x hx) i))
    (fun i => AnalyticFractionOn.of_analytic (fun x hx => analyticAt_pi_iff.mp (hb x hx) i))

end PlanarNikodym
