import PlanarNikodym.Core.Definitions
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Comp

noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal ContDiff
namespace PlanarNikodym.Family
variable {n d : ℕ} (G : PlanarNikodym.Family n d)

def hitTimes (p : Parameters n d) (E : Set Plane) : Set ℝ :=
  {t | t ∈ G.I.carrier ∧ G.graphMap p t ∈ E}

theorem image_hitTimes (p : Parameters n d) (E : Set Plane) :
    G.graphMap p '' G.hitTimes p E = G.curve p ∩ E := by
  ext q
  constructor
  · rintro ⟨t, ⟨ht, he⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, he⟩
  · rintro ⟨⟨t, ht, rfl⟩, he⟩
    exact ⟨t, ⟨ht, he⟩, rfl⟩

/-- The precise graph/parameter positive-measure bridge, without any
measurability assumption on E. Only Lipschitz regularity on the interval is used. -/
theorem graph_positive_iff_hitTimes_positive (p : Parameters n d) (E : Set Plane)
    {K : ℝ≥0} (hLip : LipschitzOnWith K (G.graphMap p) G.I.carrier) :
    0 < Measure.hausdorffMeasure 1 (G.curve p ∩ E) ↔
      0 < volume (G.hitTimes p E) := by
  have hz : Measure.hausdorffMeasure 1 (G.curve p ∩ E) = 0 ↔
      volume (G.hitTimes p E) = 0 := by
    constructor
    · intro h
      have hp := (LipschitzWith.prod_fst : LipschitzWith 1 (Prod.fst : Plane → ℝ)).hausdorffMeasure_image_le
        (d := 1) (by norm_num) (G.curve p ∩ E)
      have him : Prod.fst '' (G.curve p ∩ E) = G.hitTimes p E := by
        rw [← G.image_hitTimes, image_image]
        simp [graphMap]
      rw [him, hausdorffMeasure_real, h] at hp
      simpa using hp
    · intro h
      have hp := (hLip.mono (show G.hitTimes p E ⊆ G.I.carrier from fun _ ht => ht.1)).hausdorffMeasure_image_le
        (d := 1) (by norm_num)
      rw [G.image_hitTimes, hausdorffMeasure_real, h] at hp
      simpa using hp
  simpa only [pos_iff_ne_zero] using not_congr hz

theorem smooth_graph_lipschitz (hG : G.IsSmooth) (p : Parameters n d) (hp : p ∈ G.W) :
    ∃ K : ℝ≥0, LipschitzOnWith K (G.graphMap p) G.I.carrier := by
  unfold IsSmooth at hG
  have hγ : ContDiffOn ℝ ∞ (fun t => G.γ t p) G.I.carrier :=
    hG.comp (contDiffOn_id.prodMk contDiffOn_const) (fun t ht => ⟨ht, hp⟩)
  have hgraph : ContDiffOn ℝ ∞ (G.graphMap p) G.I.carrier :=
    contDiffOn_id.prodMk hγ
  exact hgraph.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc

theorem smooth_graph_positive_iff (hG : G.IsSmooth) (p : Parameters n d)
    (hp : p ∈ G.W) (E : Set Plane) :
    0 < Measure.hausdorffMeasure 1 (G.curve p ∩ E) ↔ 0 < volume (G.hitTimes p E) := by
  obtain ⟨K, hK⟩ := G.smooth_graph_lipschitz hG p hp
  exact G.graph_positive_iff_hitTimes_positive p E hK

/-- The parameter-time version retains the original Borel witness requirements. -/
def AdmitsNikodymByTimes : Prop :=
  ∃ E : Set Plane, ∃ F : Set (Base n),
    MeasurableSet E ∧ MeasurableSet F ∧ volume E = 0 ∧ 0 < volume F ∧
    ∀ z ∈ F, ∃ u : Aux d, (z, u) ∈ G.W ∧ 0 < volume (G.hitTimes (z, u) E)

theorem admitsNikodym_iff_byTimes (hG : G.IsSmooth) :
    G.AdmitsNikodym ↔ G.AdmitsNikodymByTimes := by
  constructor
  · rintro ⟨E, F, hE, hF, hE0, hFpos, hcurves⟩
    refine ⟨E, F, hE, hF, hE0, hFpos, ?_⟩
    intro z hz
    obtain ⟨u, hu, hpos⟩ := hcurves z hz
    exact ⟨u, hu, (G.smooth_graph_positive_iff hG (z, u) hu E).mp hpos⟩
  · rintro ⟨E, F, hE, hF, hE0, hFpos, hcurves⟩
    refine ⟨E, F, hE, hF, hE0, hFpos, ?_⟩
    intro z hz
    obtain ⟨u, hu, hpos⟩ := hcurves z hz
    exact ⟨u, hu, (G.smooth_graph_positive_iff hG (z, u) hu E).mpr hpos⟩

end PlanarNikodym.Family
