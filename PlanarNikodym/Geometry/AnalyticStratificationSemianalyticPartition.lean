import PlanarNikodym.Geometry.AnalyticStratificationClosedWindowInduction
import PlanarNikodym.Geometry.AnalyticStratificationFrontier

/-! An absolute semianalytic analytic chart stratification from the original
finite germs. A closed analytic window preserves complete frontier incidence
and strict dimension decrease without cutting or splitting existing strata. -/
noncomputable section
open Set
namespace PlanarNikodym

theorem exists_local_finite_semianalytic_chart_stratification
    {d : ℕ} {J : Type} [Fintype J] (f : J → (Fin d → ℝ) → ℝ)
    (x₀ : Fin d → ℝ) (ha : ∀ j, AnalyticAt ℝ (f j) x₀)
    (O : Set (Fin d → ℝ)) (hO : IsOpen O) (hxO : x₀ ∈ O) :
    ∃ U : Set (Fin d → ℝ), IsOpen U ∧ x₀ ∈ U ∧ closure U ⊆ O ∧ LocallySemianalytic U ∧
      ∃ (ι : Type) (_ : Fintype ι) (P : ι → AnalyticStratificationChart (Fin d → ℝ)),
        (⋃ i, (P i).image) = U ∧ Pairwise (fun i j => Disjoint (P i).image (P j).image) ∧
        (∀ i, LocallySemianalytic (P i).image) ∧ (∀ i, (P i).dim ≤ d) ∧
        (∀ i j, i ≠ j → ((P j).image ∩ closure (P i).image).Nonempty →
          (P j).image ⊆ closure (P i).image ∧ (P j).dim < (P i).dim) ∧
        ∀ i j, ∀ x ∈ (P i).image, ∀ y ∈ (P i).image,
          oneDimensionalSign (f j x) = oneDimensionalSign (f j y) := by
  classical
  obtain ⟨U, hU, hxU, hUO, hUsemi, κ, hκ, g, η, hg, hinc, href⟩ :=
    localAnalyticClosedWindowRefinement_fin d f x₀ ha O hO hxO
  let S := {s : κ → Fin 3 // (analyticStrongSignCell U g s).Nonempty}
  have hchart (s : S) : ∃ P : AnalyticStratificationChart (Fin d → ℝ),
      P.image = analyticStrongSignCell U g s ∧ P.dim = η s ∧
        closure (analyticStrongSignCell U g s) ∩ U = analyticWeakSignCell U g s := by
    rcases href.1 s with he | h
    · exact False.elim (s.property.ne_empty he)
    · exact h
  choose P hP hdim hcl using hchart
  refine ⟨U, hU, hxU, hUO, hUsemi, S, inferInstance, P, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨s, hs⟩ := mem_iUnion.mp hx
      rw [hP s] at hs
      exact hs.1
    · intro hx
      let s : κ → Fin 3 := fun k => oneDimensionalSign (g k x)
      have hs : x ∈ analyticStrongSignCell U g s := ⟨hx, fun _ => rfl⟩
      let a : S := ⟨s, x, hs⟩
      exact mem_iUnion.mpr ⟨a, (Set.ext_iff.mp (hP a) x).mpr hs⟩
  · intro s t hst
    apply Set.disjoint_left.mpr
    intro x hxs hxt
    rw [hP s] at hxs
    rw [hP t] at hxt
    apply hst
    apply Subtype.ext
    exact funext (fun k => (hxs.2 k).symm.trans (hxt.2 k))
  · intro i
    rw [hP i]
    exact analyticStrongSignCell_locallySemianalytic_of_closed_window hUsemi g hg i
  · intro i
    simpa using (P i).dim_le_finrank
  · intro i j hij hne
    have hne' : (analyticStrongSignCell U g j ∩ closure (analyticStrongSignCell U g i)).Nonempty := by
      simpa only [← hP i, ← hP j] using hne
    refine ⟨?_, ?_⟩
    · rw [hP i, hP j]
      exact analyticStrongSignCell_subset_closure_of_inter U g i j (hcl i) hne'
    · obtain ⟨z, hzj, hzi⟩ := hne'
      have hzW := (Set.ext_iff.mp (hcl i) z).mp ⟨hzi, hzj.1⟩
      have hf : polynomialThomFace j.val i.val := by
        intro k
        simpa only [hzj.2 k] using (polynomialWeakSignCondition_iff _ _).mp (hzW.2 k)
      have hneq : i.val ≠ j.val := fun he => hij (Subtype.ext he)
      have hlt := href.2 i j hneq i.property j.property hf
      rw [hdim i, hdim j]
      exact hlt
  · intro i j x hx y hy
    obtain ⟨k, hk⟩ := hinc j
    rw [hP i] at hx hy
    rw [← hk hx.1, ← hk hy.1]
    exact (hx.2 k).trans (hy.2 k).symm

end PlanarNikodym
