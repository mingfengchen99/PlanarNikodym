import PlanarNikodym.Geometry.AnalyticIntervalSeparation
import PlanarNikodym.Geometry.LinearIntervalSignClosure

/-! The one-dimensional analytic separating family with the exact relative
weak-sign closure formula. The extension and neighborhood work simultaneously
for every sign vector; no connectedness or frontier certificate is assumed. -/
noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym

theorem exists_analytic_interval_separating_family_with_frontier
    {ι : Type*} [Fintype ι] (I : Interval) (f : ι → ℝ → ℝ)
    (hf : ∀ i, AnalyticOnNhd ℝ (f i) I.carrier) :
    ∃ S : Finset ℝ, ∀ σ : (ι ⊕ S) → Fin 3,
      {x | x ∈ Ioo I.left I.right ∧
        ∀ j, oneDimensionalSign (analyticIntervalSeparatingFamily f S j x) = σ j}.OrdConnected ∧
      ({x | x ∈ Ioo I.left I.right ∧
        ∀ j, oneDimensionalSign (analyticIntervalSeparatingFamily f S j x) = σ j}.Nonempty →
        closure {x | x ∈ Ioo I.left I.right ∧
          ∀ j, oneDimensionalSign (analyticIntervalSeparatingFamily f S j x) = σ j} ∩
          Ioo I.left I.right =
        {x | x ∈ Ioo I.left I.right ∧
          ∀ j, polynomialSignCondition true (σ j) (analyticIntervalSeparatingFamily f S j x)}) := by
  classical
  obtain ⟨S, _, _, _, _, hsign⟩ := exists_analytic_interval_sign_partition I f hf
  let F := analyticIntervalSeparatingFamily f S
  let C (σ : (ι ⊕ S) → Fin 3) : Set ℝ :=
    {x | x ∈ Ioo I.left I.right ∧ ∀ j, oneDimensionalSign (F j x) = σ j}
  have he (σ : (ι ⊕ S) → Fin 3) (hne : (C σ).Nonempty) :
      C σ = linearIntervalSignCell false I S (fun z => σ (Sum.inr z)) := by
    obtain ⟨a, ha⟩ := hne
    obtain ⟨v, hv⟩ := hsign (fun z => σ (Sum.inr z))
    have haAtom : a ∈ analyticIntervalAtom I S (fun z => σ (Sum.inr z)) :=
      ⟨⟨ha.1.1.le, ha.1.2.le⟩, fun z => ha.2 (Sum.inr z)⟩
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, fun z => hx.2 (Sum.inr z)⟩
    · intro hx
      have hxAtom : x ∈ analyticIntervalAtom I S (fun z => σ (Sum.inr z)) :=
        ⟨⟨hx.1.1.le, hx.1.2.le⟩, hx.2⟩
      refine ⟨hx.1, ?_⟩
      intro j
      rcases j with i | z
      · exact (hv x hxAtom i).trans ((hv a haAtom i).symm.trans (ha.2 (Sum.inl i)))
      · exact hx.2 z
  refine ⟨S, ?_⟩
  intro σ
  change (C σ).OrdConnected ∧ ((C σ).Nonempty → _)
  constructor
  · rcases Set.eq_empty_or_nonempty (C σ) with hempty | hne
    · rw [hempty]
      exact ordConnected_empty
    · rw [he σ hne]
      exact linearIntervalSignCell_ordConnected false I S _
  · intro hne
    have hlinne : (linearIntervalSignCell false I S (fun z => σ (Sum.inr z))).Nonempty :=
      he σ hne ▸ hne
    have hclosed : IsClosed {x | x ∈ I.carrier ∧
        ∀ j, polynomialSignCondition true (σ j) (F j x)} := by
      have hj (j : ι ⊕ S) : IsClosed (I.carrier ∩
          F j ⁻¹' {r | polynomialSignCondition true (σ j) r}) :=
        (analyticOnNhd_analyticIntervalSeparatingFamily I f S hf j).continuousOn.preimage_isClosed_of_isClosed
          isClosed_Icc (isClosed_polynomialWeakSignCondition (σ j))
      have heq : {x | x ∈ I.carrier ∧ ∀ j, polynomialSignCondition true (σ j) (F j x)} =
          I.carrier ∩ ⋂ j, (I.carrier ∩ F j ⁻¹' {r | polynomialSignCondition true (σ j) r}) := by
        ext x
        simp only [mem_setOf_eq, mem_inter_iff, mem_iInter, mem_preimage]
        constructor
        · rintro ⟨hx, hz⟩
          exact ⟨hx, fun j => ⟨hx, hz j⟩⟩
        · rintro ⟨hx, hz⟩
          exact ⟨hx, fun j => (hz j).2⟩
      rw [heq]
      exact isClosed_Icc.inter (isClosed_iInter hj)
    have hclsub : closure (C σ) ⊆ {x | x ∈ I.carrier ∧
        ∀ j, polynomialSignCondition true (σ j) (F j x)} := by
      apply closure_minimal ?_ hclosed
      intro x hx
      exact ⟨⟨hx.1.1.le, hx.1.2.le⟩, fun j => polynomialSignCondition_weaken (hx.2 j)⟩
    apply Set.Subset.antisymm
    · intro x hx
      exact ⟨hx.2, (hclsub hx.1).2⟩
    · intro x hx
      refine ⟨?_, hx.1⟩
      change x ∈ closure (C σ)
      rw [he σ hne, linearIntervalSignCell_closure I S _ hlinne]
      exact ⟨⟨hx.1.1.le, hx.1.2.le⟩, fun z => hx.2 (Sum.inr z)⟩

/-- The full one-dimensional local separating conclusion, including relative
closures of every nonempty sign cell, follows from the original analytic germs. -/
theorem exists_local_oneDimensional_analytic_separating_family_with_frontier
    {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ) (x : ℝ)
    (hf : ∀ i, AnalyticAt ℝ (f i) x) :
    ∃ I : Interval, x ∈ Ioo I.left I.right ∧ ∃ S : Finset ℝ,
      (∀ j, AnalyticOnNhd ℝ (analyticIntervalSeparatingFamily f S j) I.carrier) ∧
      ∀ σ : (ι ⊕ S) → Fin 3,
        {y | y ∈ Ioo I.left I.right ∧
          ∀ j, oneDimensionalSign (analyticIntervalSeparatingFamily f S j y) = σ j}.OrdConnected ∧
        ({y | y ∈ Ioo I.left I.right ∧
          ∀ j, oneDimensionalSign (analyticIntervalSeparatingFamily f S j y) = σ j}.Nonempty →
          closure {y | y ∈ Ioo I.left I.right ∧
            ∀ j, oneDimensionalSign (analyticIntervalSeparatingFamily f S j y) = σ j} ∩
            Ioo I.left I.right =
          {y | y ∈ Ioo I.left I.right ∧
            ∀ j, polynomialSignCondition true (σ j) (analyticIntervalSeparatingFamily f S j y)}) := by
  obtain ⟨I, hx, hI⟩ := exists_analytic_interval_neighborhood f x hf
  obtain ⟨S, hS⟩ := exists_analytic_interval_separating_family_with_frontier I f hI
  exact ⟨I, hx, S, analyticOnNhd_analyticIntervalSeparatingFamily I f S hI, hS⟩

end PlanarNikodym
