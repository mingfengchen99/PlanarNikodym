import PlanarNikodym.Geometry.AnalyticFractions

/-! Open branches described by finitely many nonvanishing analytic functions
on one common original domain. Analytic fraction tests preserve this property. -/
noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def CommonAnalyticOpen (U V : Set E) : Prop :=
  ∃ (n : ℕ) (f : E → Fin n → ℝ), AnalyticOnNhd ℝ f U ∧
    ∀ x, x ∈ V ↔ x ∈ U ∧ ∀ i, f x i ≠ 0

namespace CommonAnalyticOpen

theorem self (U : Set E) : CommonAnalyticOpen U U := by
  refine ⟨0, fun _ i => Fin.elim0 i, fun _ _ => analyticAt_pi_iff.mpr (fun i => Fin.elim0 i), ?_⟩
  simp

theorem subset {U V : Set E} (h : CommonAnalyticOpen U V) : V ⊆ U := by
  obtain ⟨n, f, hf, he⟩ := h
  exact fun x hx => ((he x).mp hx).1

theorem isOpen {U V : Set E} (h : CommonAnalyticOpen U V) (hU : IsOpen U) :
    IsOpen V := by
  obtain ⟨n, f, hf, he⟩ := h
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨hxU, hn⟩ := (he x).mp hx
  have hne : ∀ᶠ y in 𝓝 x, ∀ i, f y i ≠ 0 :=
    eventually_all.mpr (fun i => ((analyticAt_pi_iff.mp (hf x hxU) i).continuousAt).eventually_ne (hn i))
  filter_upwards [hU.mem_nhds hxU, hne] with y hy hn
  exact (he y).mpr ⟨hy, hn⟩

theorem inter_fraction_ne_zero {U V : Set E} (h : CommonAnalyticOpen U V)
    {f : E → ℝ} (hf : AnalyticFractionOn U V f) :
    CommonAnalyticOpen U (V ∩ {x | f x ≠ 0}) := by
  obtain ⟨n, g, hg, he⟩ := h
  obtain ⟨p, hp, htest⟩ := hf.exists_common_analytic_zero_test
  refine ⟨n + 1, fun x => Fin.cons (p x) (g x), ?_, ?_⟩
  · intro x hx
    apply analyticAt_pi_iff.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hp x hx
    · exact analyticAt_pi_iff.mp (hg x hx) j
  · intro x
    simp only [mem_inter_iff, mem_setOf_eq, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
    constructor
    · rintro ⟨hx, hn⟩
      exact ⟨((he x).mp hx).1, (htest x hx).2.mp hn, ((he x).mp hx).2⟩
    · rintro ⟨hx, hp, hg⟩
      have hv : x ∈ V := (he x).mpr ⟨hx, hg⟩
      exact ⟨hv, (htest x hv).2.mpr hp⟩

end CommonAnalyticOpen
end PlanarNikodym
