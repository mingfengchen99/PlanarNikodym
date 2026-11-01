import PlanarNikodym.Geometry.AnalyticIntervalPartition

/-! The one-dimensional local separating-family theorem. A finite
analytic family is enlarged only by the linear functions at its actual
zero cuts. Every sign condition of the enlarged family is order connected
on one common open interval. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace PlanarNikodym

/-- Finitely many analytic germs admit one compact interval neighborhood. -/
theorem exists_analytic_interval_neighborhood {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ) (x : ℝ) (hf : ∀ i, AnalyticAt ℝ (f i) x) :
    ∃ I : Interval, x ∈ Ioo I.left I.right ∧
      ∀ i, AnalyticOnNhd ℝ (f i) I.carrier := by
  have hnear : ∀ᶠ y in 𝓝 x, ∀ i, AnalyticAt ℝ (f i) y :=
    Filter.eventually_all.mpr (fun i => (hf i).eventually_analyticAt)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let I : Interval := ⟨x - r / 2, x + r / 2, by linarith⟩
  refine ⟨I, ⟨by dsimp [I]; linarith, by dsimp [I]; linarith⟩, ?_⟩
  intro i y hy
  apply hball (y := y) _ i
  rw [Real.dist_eq, abs_lt]
  change x - r / 2 ≤ y ∧ y ≤ x + r / 2 at hy
  constructor <;> linarith [hy.1, hy.2]

/-- The enlarged family contains the original functions literally as its
left summand and the actual linear zero-cut functions as its right one. -/
def analyticIntervalSeparatingFamily {ι : Type*} (f : ι → ℝ → ℝ)
    (S : Finset ℝ) : (ι ⊕ S) → ℝ → ℝ :=
  Sum.elim f (fun z y => y - z)

theorem analyticOnNhd_analyticIntervalSeparatingFamily {ι : Type*}
    (I : Interval) (f : ι → ℝ → ℝ) (S : Finset ℝ)
    (hf : ∀ i, AnalyticOnNhd ℝ (f i) I.carrier) (j : ι ⊕ S) :
    AnalyticOnNhd ℝ (analyticIntervalSeparatingFamily f S j) I.carrier := by
  rcases j with i | z
  · exact hf i
  · intro y _
    exact analyticAt_id.sub analyticAt_const

/-- Every sign condition of the concrete enlarged family is empty or
connected on the open interval. The cuts work for all sign vectors. -/
theorem exists_analytic_interval_separating_family {ι : Type*} [Fintype ι]
    (I : Interval) (f : ι → ℝ → ℝ) (hf : ∀ i, AnalyticOnNhd ℝ (f i) I.carrier) :
    ∃ S : Finset ℝ, ∀ σ : (ι ⊕ S) → Fin 3,
      {y | y ∈ Ioo I.left I.right ∧
        ∀ j, oneDimensionalSign (analyticIntervalSeparatingFamily f S j y) = σ j}.OrdConnected := by
  classical
  obtain ⟨S, _, _, _, hconn, hsign⟩ := exists_analytic_interval_sign_partition I f hf
  refine ⟨S, fun σ => ⟨?_⟩⟩
  intro y hy z hz t ht
  let τ : S → Fin 3 := fun a => σ (Sum.inr a)
  have hyA : y ∈ analyticIntervalAtom I S τ :=
    ⟨⟨hy.1.1.le, hy.1.2.le⟩, fun a => hy.2 (Sum.inr a)⟩
  have hzA : z ∈ analyticIntervalAtom I S τ :=
    ⟨⟨hz.1.1.le, hz.1.2.le⟩, fun a => hz.2 (Sum.inr a)⟩
  have htA := (hconn τ).out hyA hzA ht
  obtain ⟨v, hv⟩ := hsign τ
  refine ⟨⟨hy.1.1.trans_le ht.1, ht.2.trans_lt hz.1.2⟩, ?_⟩
  intro j
  rcases j with i | a
  · exact (hv t htA i).trans ((hv y hyA i).symm.trans (hy.2 (Sum.inl i)))
  · exact htA.2 a

/-- A common open interval and a genuine finite analytic extension of
any finite germ family, with every sign set empty or connected. This is
the one-dimensional separating result, not a higher-dimensional input. -/
theorem exists_local_oneDimensional_analytic_separating_family
    {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ) (x : ℝ)
    (hf : ∀ i, AnalyticAt ℝ (f i) x) :
    ∃ I : Interval, x ∈ Ioo I.left I.right ∧ ∃ S : Finset ℝ,
      (∀ j, AnalyticOnNhd ℝ (analyticIntervalSeparatingFamily f S j) I.carrier) ∧
      ∀ σ : (ι ⊕ S) → Fin 3,
        {y | y ∈ Ioo I.left I.right ∧
          ∀ j, oneDimensionalSign (analyticIntervalSeparatingFamily f S j y) = σ j}.OrdConnected := by
  obtain ⟨I, hx, hI⟩ := exists_analytic_interval_neighborhood f x hf
  obtain ⟨S, hS⟩ := exists_analytic_interval_separating_family I f hI
  exact ⟨I, hx, S, analyticOnNhd_analyticIntervalSeparatingFamily I f S hI, hS⟩

end PlanarNikodym
