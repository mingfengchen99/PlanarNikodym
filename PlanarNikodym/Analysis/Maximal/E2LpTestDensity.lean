import Mathlib.MeasureTheory.Function.ContinuousMapDense
import PlanarNikodym.Analysis.Maximal.Averaging

/-! The genuine test class used for extending a maximal estimate: compactly
supported continuous functions, embedded into the ambient Lᵖ space. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

def compactContinuousLpTests_e2 (p : ℝ≥0∞) : Set (Lp ℂ p (volume : Measure (ℝ × ℝ))) :=
  {u | ∃ f : ℝ × ℝ → ℂ, Continuous f ∧ HasCompactSupport f ∧
    ∃ hf : MemLp f p volume, hf.toLp f = u}

theorem compactContinuousLpTests_e2_dense (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    Dense (compactContinuousLpTests_e2 p) := by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedEBall).2 fun ε hε => ?_
  obtain ⟨g, hgc, hdist, hcont, hgp⟩ :=
    (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le hp hε.ne'
  refine ⟨hgp.toLp g, ⟨g, hcont, hgc, hgp, rfl⟩, ?_⟩
  rwa [Metric.mem_closedEBall', ← Lp.toLp_coeFn f (Lp.memLp f), Lp.edist_toLp_toLp]

def compactContinuousLpTestRep_e2 {p : ℝ≥0∞} (u : compactContinuousLpTests_e2 p) :
    ℝ × ℝ → ℂ := Classical.choose u.property

theorem compactContinuousLpTestRep_e2_spec {p : ℝ≥0∞} (u : compactContinuousLpTests_e2 p) :
    Continuous (compactContinuousLpTestRep_e2 u) ∧
      HasCompactSupport (compactContinuousLpTestRep_e2 u) ∧
      ∃ hf : MemLp (compactContinuousLpTestRep_e2 u) p volume,
        hf.toLp (compactContinuousLpTestRep_e2 u) = u.val :=
  Classical.choose_spec u.property

theorem compactContinuousLpTestRep_e2_memLp {p : ℝ≥0∞} (u : compactContinuousLpTests_e2 p) :
    MemLp (compactContinuousLpTestRep_e2 u) p volume :=
  Classical.choose (compactContinuousLpTestRep_e2_spec u).2.2

theorem compactContinuousLpTestRep_e2_toLp {p : ℝ≥0∞} (u : compactContinuousLpTests_e2 p) :
    (compactContinuousLpTestRep_e2_memLp u).toLp (compactContinuousLpTestRep_e2 u) = u.val :=
  Classical.choose_spec (compactContinuousLpTestRep_e2_spec u).2.2

theorem compactContinuousLpTestRep_e2_integrable {p : ℝ≥0∞}
    (u : compactContinuousLpTests_e2 p) : Integrable (compactContinuousLpTestRep_e2 u) :=
  (compactContinuousLpTestRep_e2_spec u).1.integrable_of_hasCompactSupport
    (compactContinuousLpTestRep_e2_spec u).2.1

theorem compactContinuousLpTestRep_e2_bounded {p : ℝ≥0∞}
    (u : compactContinuousLpTests_e2 p) : ∃ B : ℝ, ∀ x, ‖compactContinuousLpTestRep_e2 u x‖ ≤ B := by
  obtain ⟨x₀, hx₀⟩ := (compactContinuousLpTestRep_e2_spec u).1.norm.exists_forall_ge_of_hasCompactSupport
    (compactContinuousLpTestRep_e2_spec u).2.1.norm
  exact ⟨‖compactContinuousLpTestRep_e2 u x₀‖, hx₀⟩

end PlanarNikodym
