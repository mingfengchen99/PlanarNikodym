import PlanarNikodym.Analysis.Jets.ScalarJetLpReduction
import PlanarNikodym.Analysis.Fourier.GlyzTimeTranslation

/-! Fixed time translations preserve the actual weighted scalar operator
and the input Lp norm, and transport its local geometry. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace PlanarNikodym

def scalarJetTimeTranslateCutoff {d : ℕ} (χ : Cutoff d) (s : ℝ) : Cutoff d :=
  fun x => χ (x.1 + s, x.2)

theorem contDiff_scalarJetTimeTranslateCutoff {d : ℕ} (χ : Cutoff d)
    (hχ : ContDiff ℝ ∞ χ) (s : ℝ) :
    ContDiff ℝ ∞ (scalarJetTimeTranslateCutoff χ s) :=
  hχ.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd)

theorem hasCompactSupport_scalarJetTimeTranslateCutoff {d : ℕ} (χ : Cutoff d)
    (hc : HasCompactSupport χ) (s : ℝ) :
    HasCompactSupport (scalarJetTimeTranslateCutoff χ s) := by
  have he : scalarJetTimeTranslateCutoff χ s = χ ∘ Homeomorph.addRight (s, (0 : Parameters 2 d)) := by
    funext x
    change χ (x.1 + s, x.2) = χ (x.1 + s, x.2 + 0)
    rw [add_zero]
  rw [he]
  exact hc.comp_homeomorph _

theorem scalarJetTimeTranslateCutoff_support {d : ℕ} (χ : Cutoff d) (s : ℝ)
    {x : ℝ × Parameters 2 d} (hx : x ∈ tsupport (scalarJetTimeTranslateCutoff χ s)) :
    (x.1 + s, x.2) ∈ tsupport χ :=
  tsupport_comp_subset_preimage χ
    ((continuous_fst.add continuous_const).prodMk continuous_snd) hx

/-- Translation of the physical input commutes exactly with the original
scaled convolution, without assumptions on its symbol or scale. -/
theorem scalarJet_scaledFrequencyConvolution_timeTranslate
    (a : Plane → ℝ) (f : Plane → ℂ) (s r : ℝ) (x : Plane) :
    scaledFrequencyConvolution a r (glyzTimeTranslateInput f s) x =
      scaledFrequencyConvolution a r f (x + (s, 0)) := by
  unfold scaledFrequencyConvolution
  congr 1
  have h := integral_add_right_eq_self (μ := (volume : Measure Plane))
    (fun y : Plane => inverseFourierIntegral a (r • ((x + (s, 0)) - y)) * f y) (s, 0)
  convert h using 1
  congr 1
  funext y
  have hy : (y.1 + s, y.2) = y + (s, 0) := by ext <;> simp
  change inverseFourierIntegral a (r • (x - y)) * f (y.1 + s, y.2) = _
  rw [hy, add_sub_add_right_eq_sub]

/-- The actual weighted curve average is invariant after translating
both its time cutoff and its physical input. -/
theorem Family.scalarJet_weightedAverage_timeTranslate {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (a : Plane → ℝ) (f : Plane → ℂ) (s r : ℝ) :
    (G.glyzTimeTranslate s).cutoffAverage (scalarJetTimeTranslateCutoff χ s)
      (scaledFrequencyConvolution a r (glyzTimeTranslateInput f s)) =
        G.cutoffAverage χ (scaledFrequencyConvolution a r f) := by
  funext q
  unfold Family.cutoffAverage
  simp_rw [scalarJet_scaledFrequencyConvolution_timeTranslate]
  have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun t : ℝ => (χ (t, q) : ℂ) * scaledFrequencyConvolution a r f (G.graphMap q t)) s
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [scalarJetTimeTranslateCutoff, Family.graphMap, Family.glyzTimeTranslate,
    Prod.mk_add_mk, add_zero]

theorem eLpNorm_scalarJetTimeTranslateInput {f : Plane → ℂ} {p : ℝ≥0∞}
    (hf : AEStronglyMeasurable f volume) (s : ℝ) :
    eLpNorm (glyzTimeTranslateInput f s) p volume = eLpNorm f p volume := by
  have he : glyzTimeTranslateInput f s = f ∘ (fun y : Plane => y + (s, 0)) := by
    funext y
    change f (y.1 + s, y.2) = f (y.1 + s, y.2 + 0)
    rw [add_zero]
  rw [he]
  exact eLpNorm_comp_measurePreserving hf (measurePreserving_add_right volume (s, 0))

theorem Family.analyticAt_scalarJetTimeTranslate_support {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (s : ℝ)
    (ha : ∀ x ∈ tsupport χ,
      AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x) :
    ∀ x ∈ tsupport (scalarJetTimeTranslateCutoff χ s),
      AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => (G.glyzTimeTranslate s).γ y.1 y.2) x := by
  intro x hx
  have ht : AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => (y.1 + s, y.2)) x :=
    (analyticAt_fst.add analyticAt_const).prod analyticAt_snd
  exact AnalyticAt.comp (f := fun y : ℝ × Parameters 2 d => (y.1 + s, y.2))
    (g := fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) (x := x)
    (ha _ (scalarJetTimeTranslateCutoff_support χ s hx)) ht

theorem scalarJetTimeTranslateCutoff_time_support {d : ℕ} (χ : Cutoff d) (s : ℝ)
    (ht : ∀ x ∈ tsupport χ, x.1 ∈ Ioo (s - 1) (s + 1)) :
    ∀ x ∈ tsupport (scalarJetTimeTranslateCutoff χ s), x.1 ∈ Ioo (-1 : ℝ) 1 := by
  intro x hx
  have h := ht _ (scalarJetTimeTranslateCutoff_support χ s hx)
  constructor <;> dsimp at h ⊢ <;> linarith [h.1, h.2]

end PlanarNikodym
