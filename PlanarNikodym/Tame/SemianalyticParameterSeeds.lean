import PlanarNikodym.Cells.FamilyIntrinsicRankCover
import PlanarNikodym.Cells.RankDecomposition
import PlanarNikodym.Geometry.SemianalyticAnalyticSignDomains

/-! Both literal analytic parameter seed alternatives are absolutely
semianalytic in the fixed parameter frame, including at their boundary. -/
noncomputable section
open Set Metric
namespace PlanarNikodym

theorem locallySemianalytic_parameterFrame_ball {d : ℕ}
    (c : Parameters 2 d) (r : ℝ) (hr : 0 < r) :
    LocallySemianalytic ((parameterFrame d) ⁻¹' ball c r) := by
  let e := parameterFrame d
  have hfst := (locallySemianalytic_coordinate_ball c.1 r hr).preimage_analytic
    (fun x => (e x).1) (fun x => analyticAt_fst.comp (e.analyticAt x))
  have hsnd := (locallySemianalytic_coordinate_ball c.2 r hr).preimage_analytic
    (fun x => (e x).2) (fun x => analyticAt_snd.comp (e.analyticAt x))
  have he : e ⁻¹' ball c r = (fun x => (e x).1) ⁻¹' ball c.1 r ∩
      (fun x => (e x).2) ⁻¹' ball c.2 r := by
    ext x
    simp only [mem_preimage, mem_ball, mem_inter_iff, Prod.dist_eq, max_lt_iff]
  rw [he]
  exact hfst.inter hsnd

theorem Family.analyticParameterDomain_semianalytic {d : ℕ} (G : Family 2 d)
    (hD : AnalyticParameterDomain G) :
    LocallySemianalytic ((parameterFrame d) ⁻¹' G.W) := by
  rcases hD.2.2 with ⟨c, r, hr, hW⟩ | ⟨f, hf, hW⟩
  · rw [hW]
    exact locallySemianalytic_parameterFrame_ball c r hr
  · let e := parameterFrame d
    let S := e ⁻¹' G.W
    have hcl : closure S = e ⁻¹' closure G.W :=
      (e.toHomeomorph.preimage_closure G.W).symm
    have hfa : AnalyticOnNhd ℝ (f ∘ e) (closure S) := by
      intro x hx
      have hxW : e x ∈ closure G.W := by
        change x ∈ e ⁻¹' closure G.W
        rwa [← hcl]
      exact (hf (e x) hxW).comp (e.analyticAt x)
    apply locallySemianalytic_of_sign_description_at_closure
      (fun _ : Fin 1 => f ∘ e) (fun _ => hfa) (fun s => s 0 = 0)
    intro x
    change e x ∈ G.W ↔ _
    rw [hW]
    exact oneDimensionalSign_eq_zero.symm

end PlanarNikodym
