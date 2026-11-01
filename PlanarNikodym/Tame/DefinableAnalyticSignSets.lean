import PlanarNikodym.Tame.CompactAnalyticGraphs
import PlanarNikodym.Tame.DefinableThomRoots

/-! Genuine R_an formulas for arbitrary finite Boolean analytic sign sets.
Common graph domains are constructed from the original analytic germs. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace PlanarNikodym

theorem ranDefinableOn_boolean_sign_set
    {n : ℕ} {J : Type} [Fintype J] {S : Set (Fin n → ℝ)}
    (hS : RanDefinable S) (f : J → (Fin n → ℝ) → ℝ)
    (hf : ∀ j, RanDefinableOn (f j) S) (Q : (J → Fin 3) → Prop) :
    RanDefinable {x | x ∈ S ∧ Q (fun j => oneDimensionalSign (f j x))} := by
  classical
  have hcell (s : J → Fin 3) : RanDefinable
      {x | x ∈ S ∧ ∀ j, oneDimensionalSign (f j x) = s j} := by
    convert hS.inter (Set.definable_iInter_of_finite
      (fun j => ranDefinableOn_oneDimensionalSign_eq hS (hf j) (s j))) using 1
    ext x
    simp only [mem_inter_iff, mem_iInter, mem_setOf_eq]
    aesop
  convert Set.definable_iUnion_of_finite
    (fun s : {s : J → Fin 3 // Q s} => hcell s.val) using 1
  ext x
  simp only [mem_iUnion, mem_setOf_eq]
  constructor
  · rintro ⟨hx, hQ⟩
    exact ⟨⟨fun j => oneDimensionalSign (f j x), hQ⟩, hx, fun _ => rfl⟩
  · rintro ⟨s, hx, hs⟩
    exact ⟨hx, (funext hs).symm ▸ s.property⟩

theorem exists_common_ranDefinableOn_ball_of_analytic_germs
    {n : ℕ} {J : Type} [Fintype J] (f : J → (Fin n → ℝ) → ℝ)
    (x₀ : Fin n → ℝ) (hf : ∀ j, AnalyticAt ℝ (f j) x₀)
    (O : Set (Fin n → ℝ)) (hO : IsOpen O) (hxO : x₀ ∈ O) :
    ∃ r : ℝ, 0 < r ∧ ball x₀ r ⊆ O ∧
      ∀ j, RanDefinableOn (f j) (ball x₀ r) := by
  classical
  choose r hr hgraph using fun j => exists_ranDefinableOn_ball_of_analyticAt (hf j)
  have hnear : {y | y ∈ O ∧ ∀ j, y ∈ ball x₀ (r j)} ∈ 𝓝 x₀ := by
    exact inter_mem (hO.mem_nhds hxO)
      (Filter.eventually_all.mpr (fun j => ball_mem_nhds x₀ (hr j)))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  exact ⟨δ, hδ, fun _ hy => (hδsub hy).1,
    fun j => (hgraph j).restrict (ranDefinable_ball x₀ δ) (fun _ hy => (hδsub hy).2 j)⟩

end PlanarNikodym
