import PlanarNikodym.Analysis.Jets.ScalarJetSignedCutoff
import PlanarNikodym.Analysis.Jets.ScalarJetTimeTranslation

/-! The regular open neighborhood is chosen before every cutoff and every
finite family of differentiated amplitudes. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace PlanarNikodym

/-- Local analyticity of the actual cinematic determinant follows from
local analyticity of the defining function. -/
theorem Family.scalarJet_cinematicDet_analyticAt {d : ℕ} (G : Family 2 d)
    {x : ℝ × Parameters 2 d}
    (ha : AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x) :
    AnalyticAt ℝ G.cinematicDet x := by
  apply analyticAt_det
  intro i j
  exact timeDerivative_analyticAt (G.parameterColumn_analyticAt ha j) i

/-- This neighborhood depends only on the regular point and geometry.
All later scalar and jet cutoffs may be chosen freely inside it. -/
theorem Family.exists_scalarJet_regular_neighborhood {d : ℕ} (G : Family 2 d)
    (x : ℝ × Parameters 2 d)
    (ha : AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    (hd : G.cinematicDet x ≠ 0) :
    ∃ O : Set (ℝ × Parameters 2 d), IsOpen O ∧ x ∈ O ∧
      ∀ y ∈ O,
        AnalyticAt ℝ (fun z : ℝ × Parameters 2 d => G.γ z.1 z.2) y ∧
        G.cinematicDet y ≠ 0 ∧ y.1 ∈ Ioo (x.1 - 1) (x.1 + 1) := by
  let S : Set (ℝ × Parameters 2 d) := {y |
    AnalyticAt ℝ (fun z : ℝ × Parameters 2 d => G.γ z.1 z.2) y ∧
    AnalyticAt ℝ G.cinematicDet y ∧ G.cinematicDet y ≠ 0}
  have hS : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    filter_upwards [hy.1.eventually_analyticAt, hy.2.1.eventually_analyticAt,
      hy.2.1.continuousAt.eventually_ne hy.2.2] with z hz hzd hzne
    exact ⟨hz, hzd, hzne⟩
  refine ⟨S ∩ Prod.fst ⁻¹' Ioo (x.1 - 1) (x.1 + 1),
    hS.inter (isOpen_Ioo.preimage continuous_fst), ?_, ?_⟩
  · exact ⟨⟨ha, G.scalarJet_cinematicDet_analyticAt ha, hd⟩, by constructor <;> linarith⟩
  · intro y hy
    exact ⟨hy.1.1, hy.1.2.2, hy.2⟩

end PlanarNikodym
