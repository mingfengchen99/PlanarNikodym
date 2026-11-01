import PlanarNikodym.Geometry.AnalyticStratificationChartTopology
import PlanarNikodym.Cells.CompactExceptionalImages

/-! Metric dimensions of the constructed actual analytic charts. Local
C1 bounds suffice on their open source domains; no compact parameter
extension or convex source is assumed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
namespace PlanarNikodym

theorem AnalyticStratificationChart.dimH_image_le {n : ℕ}
    (P : AnalyticStratificationChart (Fin n → ℝ)) : dimH P.image ≤ P.dim := by
  have hLip : dimH P.image ≤ dimH P.source := by
    apply dimH_image_le_of_locally_lipschitzOn
    intro x hx
    have hc : ContDiffAt ℝ 1 P.map x := (P.analytic_map x hx).contDiffAt
    obtain ⟨C, V, hV, hL⟩ := hc.exists_lipschitzOnWith
    exact ⟨C, V, mem_nhdsWithin_of_mem_nhds hV, hL⟩
  calc
    dimH P.image ≤ dimH P.source := hLip
    _ ≤ dimH (univ : Set (Fin P.dim → ℝ)) := dimH_mono (subset_univ _)
    _ = P.dim := by simp only [Real.dimH_univ_eq_finrank, Module.finrank_pi,
        Fintype.card_fin]

theorem AnalyticStratificationChart.linear_image_null_of_dim_lt_two {n : ℕ}
    (P : AnalyticStratificationChart (Fin n → ℝ))
    (L : (Fin n → ℝ) →L[ℝ] Base 2) (hd : P.dim < 2) :
    volume (L '' P.image) = 0 := by
  have hdim : dimH (L '' P.image) < (2 : ℝ≥0∞) :=
    (L.lipschitz.dimH_image_le P.image).trans_lt
      (P.dimH_image_le.trans_lt (by exact_mod_cast hd))
  have hz := hausdorffMeasure_of_dimH_lt (d := (2 : ℝ≥0)) hdim
  have he := hausdorffMeasure_pi_real (ι := Fin 2)
  norm_num only [Fintype.card_fin, Nat.cast_ofNat, NNReal.coe_ofNat] at hz he
  rw [he] at hz
  exact hz

end PlanarNikodym
