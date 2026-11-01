import PlanarNikodym.Analysis.Jets.JetAmplitudeBounds
import PlanarNikodym.Analysis.Fourier.FourierCharacterJets

/-! Actual frequency-symbol bounds for the finite amplitudes and their
time integrals. These polynomial bounds do not assert local smoothing. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace PlanarNikodym

/-- The full finite amplitude of a pure frequency has polynomial growth,
with one constant uniform over frequency and all parameter points. -/
theorem Family.exists_uniform_cutoffJetAmplitude_fourierCharacter_bound
    {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ξ : Plane) (z : Base 2) (t : ℝ) (u : Aux d),
      ‖G.cutoffJetAmplitude χ (fun x => planeFourierCharacter x ξ) j z t u‖ ≤
        C * (1 + ‖ξ‖) ^ j := by
  obtain ⟨A, hA, hAmp⟩ := G.exists_uniform_cutoffJetAmplitude_bound χ hχ hc hγ j
  let B : ℝ := ((j + 1 : ℕ) : ℝ) * (1 + 4 * Real.pi) ^ j
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨A * B, mul_pos hA hB, ?_⟩
  intro ξ z t u
  calc
    _ ≤ A * ∑ m ∈ Finset.range (j + 1),
        ‖iteratedFDeriv ℝ m (fun x => planeFourierCharacter x ξ) (G.graphMap (z, u) t)‖ :=
      hAmp _ (planeFourierCharacter_contDiff ξ) z t u
    _ ≤ A * (B * (1 + ‖ξ‖) ^ j) :=
      mul_le_mul_of_nonneg_left
        (sum_norm_iteratedFDeriv_planeFourierCharacter_le ξ (G.graphMap (z, u) t) j) hA.le
    _ = _ := by ring

/-- The actual auxiliary derivative of the oscillatory time integral is
the integral of the already constructed finite multilinear amplitude. -/
theorem Family.auxiliary_cutoffOscillatoryJet_eq_integral_amplitude
    {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (ξ : Plane) (j : ℕ) (z : Base 2) (u : Aux d) :
    iteratedFDeriv ℝ j (fun v => G.cutoffOscillatoryAmplitude χ (z, v) ξ) u =
      ∫ t : ℝ, G.cutoffJetAmplitude χ (fun x => planeFourierCharacter x ξ) j z t u := by
  exact G.auxiliary_cutoffJet_eq_integral_amplitude χ hχ hc hγ
    (planeFourierCharacter_contDiff ξ) j z u

/-- Compactness of the true time projection gives a parameter-independent
bound for every auxiliary jet of the actual oscillatory amplitude. -/
theorem Family.exists_uniform_auxiliary_cutoffOscillatoryJet_bound
    {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x) (j : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (ξ : Plane) (z : Base 2) (u : Aux d),
      ‖iteratedFDeriv ℝ j (fun v => G.cutoffOscillatoryAmplitude χ (z, v) ξ) u‖ ≤
        D * (1 + ‖ξ‖) ^ j := by
  classical
  obtain ⟨C, hC, hAmp⟩ :=
    G.exists_uniform_cutoffJetAmplitude_fourierCharacter_bound χ hχ hc hγ j
  let T : Set ℝ := Prod.fst '' tsupport χ
  have hT : IsCompact T := hc.isCompact.image continuous_fst
  let D : ℝ := C * (volume.real T + 1)
  have hD : 0 < D := by dsimp [D]; exact mul_pos hC (by positivity)
  refine ⟨D, hD, ?_⟩
  intro ξ z u
  let P : ℝ := (1 + ‖ξ‖) ^ j
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hi : Integrable (fun t : ℝ => T.indicator (fun _ => C * P) t) :=
    (integrableOn_const hT.measure_ne_top).integrable_indicator hT.measurableSet
  have hpoint (t : ℝ) :
      ‖G.cutoffJetAmplitude χ (fun x => planeFourierCharacter x ξ) j z t u‖ ≤
        T.indicator (fun _ => C * P) t := by
    by_cases ht : t ∈ T
    · simpa only [indicator_of_mem ht, P] using hAmp ξ z t u
    · have hx : (t, (z, u)) ∉ tsupport χ := by
        intro hx
        exact ht ⟨(t, (z, u)), hx, rfl⟩
      simp only [Family.cutoffJetAmplitude, if_neg hx, norm_zero,
        indicator_of_notMem ht, le_refl]
  rw [G.auxiliary_cutoffOscillatoryJet_eq_integral_amplitude χ hχ hc hγ ξ j z u]
  calc
    _ ≤ ∫ t : ℝ, ‖G.cutoffJetAmplitude χ (fun x => planeFourierCharacter x ξ) j z t u‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, T.indicator (fun _ => C * P) t := integral_mono
      (G.cutoffJetAmplitude_integrable χ hχ hc hγ (planeFourierCharacter_contDiff ξ) j z u).norm
      hi hpoint
    _ = volume.real T * (C * P) := by rw [integral_indicator_const _ hT.measurableSet, smul_eq_mul]
    _ ≤ D * (1 + ‖ξ‖) ^ j := by dsimp [D, P]; nlinarith

end PlanarNikodym
