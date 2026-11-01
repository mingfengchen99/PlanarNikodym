import PlanarNikodym.Geometry.AnalyticStratificationDimensioned
import PlanarNikodym.Geometry.SemianalyticGerms
import PlanarNikodym.Geometry.SemianalyticCylinders

/-! A closed analytic window prevents any boundary ambiguity when promoting
the constructed sign strata to absolute semianalytic sets. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace PlanarNikodym

def LocalAnalyticClosedWindowRefinement (d : ℕ) : Prop :=
  ∀ {J : Type} [Fintype J] (f : J → (Fin d → ℝ) → ℝ) (x₀ : Fin d → ℝ),
    (∀ j, AnalyticAt ℝ (f j) x₀) →
    ∀ O : Set (Fin d → ℝ), IsOpen O → x₀ ∈ O →
    ∃ U : Set (Fin d → ℝ), IsOpen U ∧ x₀ ∈ U ∧ closure U ⊆ O ∧
      LocallySemianalytic U ∧
      ∃ (κ : Type) (_ : Fintype κ) (g : κ → (Fin d → ℝ) → ℝ)
        (η : (κ → Fin 3) → ℕ),
        (∀ k, AnalyticOnNhd ℝ (g k) (closure U)) ∧
        (∀ j, ∃ k, EqOn (g k) (f j) U) ∧ AnalyticDimensionedSignCells U g η

theorem analyticStrongSignCell_locallySemianalytic_of_closed_window
    {d : ℕ} {J : Type} [Fintype J] {U : Set (Fin d → ℝ)}
    (hU : LocallySemianalytic U) (g : J → (Fin d → ℝ) → ℝ)
    (hg : ∀ j, AnalyticOnNhd ℝ (g j) (closure U)) (s : J → Fin 3) :
    LocallySemianalytic (analyticStrongSignCell U g s) := by
  intro x
  by_cases hx : x ∈ closure U
  · have hsign := semianalyticAt_of_analytic_sign_germs g (fun j => hg j x hx)
      (fun t => t = s)
    have hUx : SemianalyticAt U x := hU x
    have hi := hUx.inter hsign
    exact hi.congr (Filter.Eventually.of_forall (fun y => by
      simp only [mem_inter_iff, mem_setOf_eq, analyticStrongSignCell]
      exact and_congr_right (fun _ => funext_iff)))
  · have hnear : ∀ᶠ y in 𝓝 x, y ∉ closure U := isClosed_closure.isOpen_compl.mem_nhds hx
    have hempty : SemianalyticAt (∅ : Set (Fin d → ℝ)) x :=
      ⟨univ, isOpen_univ, mem_univ _, Empty, inferInstance, Empty.elim,
        (fun j => Empty.elim j), (fun _ => False), fun _ _ => Iff.rfl⟩
    apply hempty.congr
    filter_upwards [hnear] with y hy
    simp only [mem_empty_iff_false, false_iff]
    intro hc
    exact hy (subset_closure hc.1)

end PlanarNikodym
