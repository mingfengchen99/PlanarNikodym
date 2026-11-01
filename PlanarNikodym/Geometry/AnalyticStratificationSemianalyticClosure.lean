import PlanarNikodym.Geometry.AnalyticStratificationFrontierUnions

/-! Closure, interior and frontier preserve genuine semianalyticity.
The closure proof uses the actual finite compatible analytic stratification. -/
noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym

theorem SemianalyticAt.closure {d : ℕ} {A : Set (Fin d → ℝ)} {x₀ : Fin d → ℝ}
    (hA : SemianalyticAt A x₀) : SemianalyticAt (_root_.closure A) x₀ := by
  classical
  obtain ⟨U, hU, hxU, _, _, ι, hι, P, hcover, _, hsemi, _, hfront, hrep⟩ :=
    exists_local_finite_semianalytic_stratification (fun _ : Unit => A) x₀
      (fun _ => hA) univ isOpen_univ (mem_univ _)
  let T := {i : ι // (P i).image ⊆ A}
  let R : Set (Fin d → ℝ) := ⋃ i : T, _root_.closure (P i.val).image ∩ U
  have hR : LocallySemianalytic R := LocallySemianalytic.iUnion _ (fun i =>
    semianalytic_stratum_relative_closure P hcover hsemi
      (fun a b hab hne => (hfront a b hab hne).1) i.val)
  have hecl : _root_.closure (A ∩ U) = ⋃ i : T, _root_.closure (P i.val).image := by
    rw [hrep (), closure_iUnion_of_finite]
  have he (y : Fin d → ℝ) (hyU : y ∈ U) : y ∈ _root_.closure A ↔ y ∈ R := by
    constructor
    · intro hy
      have hy' := hU.closure_inter ⟨hy, hyU⟩
      rw [hecl] at hy'
      obtain ⟨i, hyi⟩ := mem_iUnion.mp hy'
      exact mem_iUnion.mpr ⟨i, hyi, hyU⟩
    · intro hy
      obtain ⟨i, hyi⟩ := mem_iUnion.mp hy
      exact closure_mono i.property hyi.1
  have hRx : SemianalyticAt R x₀ := hR x₀
  apply hRx.congr
  filter_upwards [hU.mem_nhds hxU] with y hy
  exact (he y hy).symm

theorem LocallySemianalytic.closure {d : ℕ} {A : Set (Fin d → ℝ)}
    (hA : LocallySemianalytic A) : LocallySemianalytic (_root_.closure A) :=
  fun x => SemianalyticAt.closure (hA x)

theorem LocallySemianalytic.interior {d : ℕ} {A : Set (Fin d → ℝ)}
    (hA : LocallySemianalytic A) : LocallySemianalytic (interior A) := by
  simpa only [closure_compl, compl_compl] using hA.compl.closure.compl

theorem LocallySemianalytic.frontier {d : ℕ} {A : Set (Fin d → ℝ)}
    (hA : LocallySemianalytic A) : LocallySemianalytic (frontier A) := by
  rw [frontier_eq_closure_inter_closure]
  exact hA.closure.inter hA.compl.closure

end PlanarNikodym
