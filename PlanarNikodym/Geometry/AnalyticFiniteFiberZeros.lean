import PlanarNikodym.Geometry.WeierstrassPreparation
import PlanarNikodym.Geometry.WeierstrassPolynomial

/-! A local uniform finite-fiber consequence of actual convergent preparation.
The neighborhoods are chosen before the neighboring parameter, and the bound
is the order of the distinguished fiber, including order zero. -/
noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym

/-- A finite nonzero vertical order gives one product neighborhood on which every
vertical zero fiber is finite, with at most that many distinct roots. -/
theorem exists_uniform_finite_analytic_fiber_zeros
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E × ℝ → ℝ) (x₀ : E) (t₀ : ℝ) (m : ℕ)
    (hf : AnalyticAt ℝ f (x₀, t₀))
    (hzero : ∀ j < m, iteratedDeriv j (fun t => f (x₀, t)) t₀ = 0)
    (hm : iteratedDeriv m (fun t => f (x₀, t)) t₀ ≠ 0) :
    ∃ U : Set E, ∃ V : Set ℝ,
      IsOpen U ∧ x₀ ∈ U ∧ IsOpen V ∧ t₀ ∈ V ∧
      ∀ x ∈ U, {t : ℝ | t ∈ V ∧ f (x, t) = 0}.Finite ∧
        {t : ℝ | t ∈ V ∧ f (x, t) = 0}.ncard ≤ m := by
  obtain ⟨a, u, _, _, _, _, hfactor⟩ :=
    exists_analytic_weierstrass_preparation f x₀ t₀ m hf hzero hm
  obtain ⟨U, V, hU, hxU, hV, htV, hUV⟩ := mem_nhds_prod_iff'.mp hfactor
  refine ⟨U, V, hU, hxU, hV, htV, ?_⟩
  intro x hx
  obtain ⟨hfin, hcard⟩ := weierstrassPolynomial_finite_roots (a x) t₀
  have hsub : {t : ℝ | t ∈ V ∧ f (x, t) = 0} ⊆
      {t : ℝ | (t - t₀) ^ m + ∑ i : Fin m, a x i * (t - t₀) ^ (i : ℕ) = 0} := by
    intro t ht
    obtain ⟨hu, he⟩ := hUV (show (x, t) ∈ U ×ˢ V from ⟨hx, ht.1⟩)
    exact (mul_eq_zero.mp (he.symm.trans ht.2)).resolve_right hu
  exact ⟨hfin.subset hsub, (Set.ncard_le_ncard hsub hfin).trans hcard⟩

/-- The order and the uniform finite-fiber neighborhood are constructed from
nonflatness of the actual distinguished fiber; no derivative order is supplied. -/
theorem exists_uniform_finite_analytic_fiber_zeros_of_nonflat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E × ℝ → ℝ) (x₀ : E) (t₀ : ℝ)
    (hf : AnalyticAt ℝ f (x₀, t₀))
    (hnf : ¬ ∀ᶠ t in 𝓝 t₀, f (x₀, t) = 0) :
    ∃ m : ℕ, ∃ U : Set E, ∃ V : Set ℝ,
      IsOpen U ∧ x₀ ∈ U ∧ IsOpen V ∧ t₀ ∈ V ∧
      ∀ x ∈ U, {t : ℝ | t ∈ V ∧ f (x, t) = 0}.Finite ∧
        {t : ℝ | t ∈ V ∧ f (x, t) = 0}.ncard ≤ m := by
  have hbase : AnalyticAt ℝ (fun t => f (x₀, t)) t₀ :=
    hf.comp (analyticAt_const.prod analyticAt_id)
  have horder : analyticOrderAt (fun t => f (x₀, t)) t₀ ≠ ⊤ :=
    fun h => hnf (analyticOrderAt_eq_top.mp h)
  obtain ⟨hzero, hm⟩ :=
    (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hbase).mp
      (Nat.cast_analyticOrderNatAt horder).symm
  exact ⟨_, exists_uniform_finite_analytic_fiber_zeros f x₀ t₀ _ hf hzero hm⟩

end PlanarNikodym
