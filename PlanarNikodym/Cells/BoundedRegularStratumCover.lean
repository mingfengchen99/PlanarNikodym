import PlanarNikodym.Geometry.AnalyticRegularSemianalyticStratification
import PlanarNikodym.Tame.DefinableSemianalyticComponents

/-! Actual finite analytic chart covers of bounded semianalytic sets.
Compactness is applied to the ambient closure; every selected chart image
is contained in the original set. The resulting global cover may overlap. -/
noncomputable section
open Set
namespace PlanarNikodym

theorem LocallySemianalytic.exists_finite_regular_analytic_chart_cover
    {d : ℕ} {A : Set (Fin d → ℝ)} (hA : LocallySemianalytic A)
    (hb : Bornology.IsBounded A) (O : Set (Fin d → ℝ))
    (hO : IsOpen O) (hAO : closure A ⊆ O) :
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → AnalyticStratificationChart (Fin d → ℝ)),
      (⋃ i, (P i).image) = A ∧
      (∀ i, LocallySemianalytic (P i).image) ∧
      (∀ i, RanDefinable (P i).image) ∧ (∀ i, (P i).dim ≤ d) ∧
      ∀ i, ∃ U : Set (Fin d → ℝ), IsOpen U ∧ (P i).image ⊆ U ∧ closure U ⊆ O ∧
        RegularStratumEquations (closure U) (P i).image (P i).dim := by
  classical
  have hlocal (x : closure A) := exists_local_finite_regular_semianalytic_stratification
    (fun _ : Fin 1 => A) x.val (fun _ => hA x.val) O hO (hAO x.property)
  choose U hU hxU hcl hsemi I hI P hcover hdisj hPsemi hdim hfront hcompatible hregular using hlocal
  letI (x : closure A) : Fintype (I x) := hI x
  obtain ⟨s, hs⟩ := hb.isCompact_closure.elim_finite_subcover U hU (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxU _⟩)
  let J := (x : s) × {i : I x.val // (P x.val i).image ⊆ A}
  let Q (j : J) := P j.1.val j.2.val
  have hQA (j : J) : (Q j).image ⊆ A := j.2.property
  refine ⟨J, inferInstance, Q, ?_, ?_, ?_, ?_, ?_⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨j, hj⟩ := mem_iUnion.mp hz
      exact hQA j hj
    · intro hz
      obtain ⟨x, hxs, hzx⟩ := mem_iUnion₂.mp (hs (subset_closure hz))
      have hzi : z ∈ A ∩ U x := ⟨hz, hzx⟩
      rw [hcompatible x 0] at hzi
      obtain ⟨i, hzi⟩ := mem_iUnion.mp hzi
      exact mem_iUnion.mpr ⟨⟨⟨x, hxs⟩, i⟩, hzi⟩
  · intro j
    exact hPsemi j.1.val j.2.val
  · intro j
    exact (hPsemi j.1.val j.2.val).ranDefinable_of_bounded (hb.subset (hQA j))
  · intro j
    exact hdim j.1.val j.2.val

  · intro j
    refine ⟨U j.1.val, hU j.1.val, ?_, hcl j.1.val, hregular j.1.val j.2.val⟩
    intro y hy
    rw [← hcover j.1.val]
    exact mem_iUnion.mpr ⟨j.2.val, hy⟩

end PlanarNikodym
