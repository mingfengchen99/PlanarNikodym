import PlanarNikodym.Analysis.Maximal.SmoothOpenApproximation
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
namespace PlanarNikodym

/-- Zero extension from an open set preserves lower semicontinuity for
nonnegative extended-valued continuous functions. -/
theorem lowerSemicontinuous_indicator_of_continuousOn {X : Type*}
    [TopologicalSpace X] {U : Set X} (hU : IsOpen U) {F : X → ℝ≥0∞}
    (hF : ContinuousOn F U) : LowerSemicontinuous (U.indicator F) := by
  classical
  intro x a ha
  by_cases hx : x ∈ U
  · rw [indicator_of_mem hx] at ha
    have hcont := hF.continuousAt (hU.mem_nhds hx)
    filter_upwards [hU.mem_nhds hx, hcont.eventually (lt_mem_nhds ha)] with y hy hya
    simpa only [indicator_of_mem hy] using hya
  · simp only [indicator_of_notMem hx, not_lt_zero] at ha

namespace Family
variable {d : ℕ} (G : Family 2 d)

/-- Continuity is only required where the actual time cutoff can be nonzero.
No global regularity of the ambient extension is assumed. -/
theorem continuous_cutoffIntegrand {χ : Cutoff d} (hχ : Continuous χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : Continuous f) :
    Continuous (fun x : ℝ × Parameters 2 d => (χ x : ℂ) * f (x.1, G.γ x.1 x.2)) := by
  apply continuous_of_tsupport
  intro x hx
  have hsub : tsupport (fun x : ℝ × Parameters 2 d =>
      (χ x : ℂ) * f (x.1, G.γ x.1 x.2)) ⊆ tsupport χ := by
    exact tsupport_mul_subset_left.trans
      (tsupport_comp_subset (g := Complex.ofReal) (by simp) χ)
  exact (Complex.continuous_ofReal.continuousAt.comp hχ.continuousAt).mul
    (hf.continuousAt.comp (continuousAt_fst.prodMk (hγ x (hsub hx))))

theorem continuous_cutoffAverage {χ : Cutoff d} (hχ : Continuous χ)
    (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : Continuous f) : Continuous (G.cutoffAverage χ f) := by
  let T : Set ℝ := Prod.fst '' tsupport χ
  have hT : IsCompact T := hc.image continuous_fst
  have hF : Continuous (fun x : Parameters 2 d × ℝ =>
      (χ (x.2, x.1) : ℂ) * f (G.graphMap x.1 x.2)) :=
    (G.continuous_cutoffIntegrand hχ hγ hf).comp (continuous_snd.prodMk continuous_fst)
  rw [← continuousOn_univ]
  exact continuousOn_integral_of_compact_support hT hF.continuousOn (by
    intro p t _ ht
    have hz : χ (t, p) = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => ht ⟨(t, p), h, rfl⟩)
    simp [hz])

/-- The auxiliary supremum is pointwise and possibly infinite. Its lower
semicontinuity supplies Borel measurability without measurable selection. -/
theorem lowerSemicontinuous_cutoffMaximal {χ : Cutoff d} {f : Plane → ℂ}
    (hA : Continuous (G.cutoffAverage χ f)) : LowerSemicontinuous (G.cutoffMaximal χ f) := by
  apply lowerSemicontinuous_iSup
  intro u
  exact ((hA.comp (continuous_id.prodMk continuous_const)).enorm).lowerSemicontinuous

theorem measurable_cutoffMaximal {χ : Cutoff d} {f : Plane → ℂ}
    (hA : Continuous (G.cutoffAverage χ f)) : Measurable (G.cutoffMaximal χ f) :=
  (G.lowerSemicontinuous_cutoffMaximal hA).measurable

theorem continuousOn_intervalAverage (U : Set (Parameters 2 d)) (hU : U ⊆ G.W)
    (hs : G.IsSmooth) {f : Plane → ℝ} (hf : Continuous f)
    (hb : ∀ x, ‖f x‖ ≤ 1) :
    ContinuousOn (fun p => ∫ t in G.I.carrier, f (G.graphMap p t)) U := by
  apply continuousOn_of_dominated (bound := fun _ => (1 : ℝ))
  · intro p hp
    obtain ⟨K, hK⟩ := G.smooth_graph_lipschitz hs p (hU hp)
    exact (hf.comp_continuousOn hK.continuousOn).aestronglyMeasurable measurableSet_Icc
  · intro p _
    exact ae_of_all _ (fun t => hb (G.graphMap p t))
  · exact integrableOn_const isCompact_Icc.measure_lt_top.ne
  · filter_upwards [ae_restrict_mem (show MeasurableSet G.I.carrier from measurableSet_Icc)]
      with t ht
    apply hf.comp_continuousOn
    apply continuousOn_const.prodMk
    exact hs.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
      (fun p hp => ⟨ht, hU hp⟩)

theorem continuousOn_positiveAverage (U : Set (Parameters 2 d)) (hU : U ⊆ G.W)
    (hs : G.IsSmooth) {f : Plane → ℝ} (hf : Continuous f)
    (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) :
    ContinuousOn (G.positiveAverage (fun x => ENNReal.ofReal (f x))) U := by
  have hb (x : Plane) : ‖f x‖ ≤ 1 := by rw [Real.norm_of_nonneg (h0 x)]; exact h1 x
  have hc := ENNReal.continuous_ofReal.comp_continuousOn
    (G.continuousOn_intervalAverage U hU hs hf hb)
  apply hc.congr
  intro p hp
  obtain ⟨K, hK⟩ := G.smooth_graph_lipschitz hs p (hU hp)
  have hi : IntegrableOn (fun t => f (G.graphMap p t)) G.I.carrier :=
    (integrableOn_const (C := (1 : ℝ)) isCompact_Icc.measure_lt_top.ne).mono'
      ((hf.comp_continuousOn hK.continuousOn).aestronglyMeasurable measurableSet_Icc)
      (ae_of_all _ (fun t => hb (G.graphMap p t)))
  exact (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun t => h0 _))).symm

/-- Borel measurability of the nonnegative maximal function on an open
parameter domain, under the actual interval regularity of the family. -/
theorem lowerSemicontinuous_positiveMaximal (U : Set (Parameters 2 d))
    (hopen : IsOpen U) (hU : U ⊆ G.W) (hs : G.IsSmooth)
    {f : Plane → ℝ} (hf : Continuous f) (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) :
    LowerSemicontinuous (G.positiveMaximal U (fun x => ENNReal.ofReal (f x))) := by
  classical
  have he : G.positiveMaximal U (fun x => ENNReal.ofReal (f x)) =
      fun z => ⨆ u : Aux d, U.indicator (G.positiveAverage (fun x => ENNReal.ofReal (f x))) (z, u) := by
    funext z
    unfold positiveMaximal
    congr 1
    funext u
    by_cases hu : (z, u) ∈ U <;> simp [hu]
  rw [he]
  apply lowerSemicontinuous_iSup
  intro u
  exact (lowerSemicontinuous_indicator_of_continuousOn hopen
    (G.continuousOn_positiveAverage U hU hs hf h0 h1)).comp
      (continuous_id.prodMk continuous_const)

theorem measurable_positiveMaximal (U : Set (Parameters 2 d))
    (hopen : IsOpen U) (hU : U ⊆ G.W) (hs : G.IsSmooth)
    {f : Plane → ℝ} (hf : Continuous f) (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) :
    Measurable (G.positiveMaximal U (fun x => ENNReal.ofReal (f x))) :=
  (G.lowerSemicontinuous_positiveMaximal U hopen hU hs hf h0 h1).measurable

end Family
end PlanarNikodym
