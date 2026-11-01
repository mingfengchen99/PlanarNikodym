import PlanarNikodym.Analysis.Fourier.NonstationaryPhase
import PlanarNikodym.Analysis.Fourier.MicrolocalSplit

/-! Connecting actual one-dimensional nonstationary phase to the true curve
Fourier amplitude and its microlocal error frequencies. Constants here are
for a fixed parameter and fixed normalized frequency; they are not uniform
over either variable. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace PlanarNikodym

/-- The phase normalized so that its oscillation parameter is precisely the
real dilation of the frequency, with the Fourier factor `2π` included. -/
def Family.normalizedGraphPhase {d : ℕ} (G : Family 2 d) (q : Parameters 2 d)
    (ξ : Plane) (t : ℝ) : ℝ := 2 * Real.pi * G.graphPhase q ξ t

theorem Family.contDiffAt_graphPhase {d : ℕ} (G : Family 2 d)
    {q : Parameters 2 d} {t : ℝ}
    (hγ : ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) (t, q))
    (ξ : Plane) : ContDiffAt ℝ ∞ (G.graphPhase q ξ) t := by
  have hs : ContDiffAt ℝ ∞ (fun s : ℝ => G.γ s q) t :=
    hγ.comp t (f := fun s : ℝ => (s, q)) (contDiffAt_id.prodMk contDiffAt_const)
  change ContDiffAt ℝ ∞ (fun s : ℝ => s * ξ.1 + G.γ s q * ξ.2) t
  exact (contDiffAt_id.mul contDiffAt_const).add (hs.mul contDiffAt_const)

theorem Family.planeFourierCharacter_eq_phaseOscillation {d : ℕ} (G : Family 2 d)
    (q : Parameters 2 d) (ξ : Plane) (r t : ℝ) :
    planeFourierCharacter (G.graphMap q t) (r • ξ) =
      phaseOscillation (G.normalizedGraphPhase q ξ) r t := by
  have he : 2 * Real.pi * fourierPhase (G.graphMap q t) (r • ξ) =
      r * G.normalizedGraphPhase q ξ t := by
    change 2 * Real.pi * ((G.graphMap q t).1 * (r * ξ.1) +
        (G.graphMap q t).2 * (r * ξ.2)) =
      r * (2 * Real.pi * ((G.graphMap q t).1 * ξ.1 + (G.graphMap q t).2 * ξ.2))
    ring
  unfold planeFourierCharacter phaseOscillation
  rw [he]

/-- Exact identification with the integral used by the integration-by-parts
theorem, including both its sign and `2π` normalization. -/
theorem Family.cutoffOscillatoryAmplitude_eq_phaseOscillation_integral {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (q : Parameters 2 d) (ξ : Plane) (r : ℝ) :
    G.cutoffOscillatoryAmplitude χ q (r • ξ) =
      ∫ t : ℝ, phaseOscillation (G.normalizedGraphPhase q ξ) r t * (χ (t, q) : ℂ) := by
  unfold Family.cutoffOscillatoryAmplitude
  simp_rw [G.planeFourierCharacter_eq_phaseOscillation q ξ r]
  apply integral_congr_ae
  filter_upwards [] with t
  ring

theorem cutoffSlice_complex_tsupport_lift {d : ℕ} (χ : Cutoff d) (q : Parameters 2 d)
    {t : ℝ} (ht : t ∈ tsupport (fun s : ℝ => (χ (s, q) : ℂ))) :
    (t, q) ∈ tsupport χ := by
  have he : tsupport (fun s : ℝ => (χ (s, q) : ℂ)) =
      tsupport (fun s : ℝ => χ (s, q)) := by
    unfold tsupport
    congr 1
    ext s
    simp
  exact tsupport_comp_subset_preimage χ (continuous_id.prodMk continuous_const) (he ▸ ht)

/-- At a fixed parameter and a fixed nonstationary frequency direction, the
actual curve Fourier amplitude decays to every algebraic order. -/
theorem Family.cutoffOscillatoryAmplitude_nonstationary_decay {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (q : Parameters 2 d) (ξ : Plane)
    (hne : ∀ t : ℝ, (t, q) ∈ tsupport χ → deriv (G.graphPhase q ξ) t ≠ 0) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, r ≠ 0 →
      ‖G.cutoffOscillatoryAmplitude χ q (r • ξ)‖ ≤ C * (|r|⁻¹) ^ n := by
  let a : ℝ → ℂ := fun t => (χ (t, q) : ℂ)
  let φ : ℝ → ℝ := G.normalizedGraphPhase q ξ
  have ha : ContDiff ℝ ∞ a := Complex.ofRealCLM.contDiff.comp
    (hχ.comp (contDiff_id.prodMk contDiff_const))
  have hca : HasCompactSupport a :=
    (cutoffSlice_hasCompactSupport χ hc q).comp_left (g := Complex.ofRealCLM) rfl
  have hφ : ∀ t ∈ tsupport a, ContDiffAt ℝ ∞ φ t := by
    intro t ht
    exact contDiffAt_const.mul
      (G.contDiffAt_graphPhase (hγ (t, q) (cutoffSlice_complex_tsupport_lift χ q ht)) ξ)
  have hφne : ∀ t ∈ tsupport a, deriv φ t ≠ 0 := by
    intro t ht
    have hmem := cutoffSlice_complex_tsupport_lift χ q ht
    have hp := (G.contDiffAt_graphPhase (hγ (t, q) hmem) ξ).differentiableAt (by simp)
    rw [show deriv φ t = (2 * Real.pi) * deriv (G.graphPhase q ξ) t from
      (hp.hasDerivAt.const_mul (2 * Real.pi)).deriv]
    exact mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (hne t hmem)
  obtain ⟨C, hC, hbound⟩ := exists_nonstationary_decay_constant hφ ha hca hφne n
  refine ⟨C, hC, ?_⟩
  intro r hr
  rw [G.cutoffOscillatoryAmplitude_eq_phaseOscillation_integral χ q ξ r]
  exact hbound r hr

/-- Apply the fixed-direction decay theorem to any actual symbol whose
topological support has the positive lower bound produced by the split. -/
theorem Family.cutoffOscillatoryAmplitude_errorSymbol_decay {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (m : Plane → ℝ)
    (hm : ∀ ξ ∈ tsupport m, ∀ x ∈ tsupport χ,
      1 / 2 ≤ |deriv (G.graphPhase x.2 ξ) x.1|)
    {ξ : Plane} (hξ : ξ ∈ tsupport m) (q : Parameters 2 d) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, r ≠ 0 →
      ‖G.cutoffOscillatoryAmplitude χ q (r • ξ)‖ ≤ C * (|r|⁻¹) ^ n := by
  apply G.cutoffOscillatoryAmplitude_nonstationary_decay χ hχ hc hγ q ξ _ n
  intro t ht
  have h := hm ξ hξ (t, q) ht
  intro hz
  simp only [hz, abs_zero] at h
  linarith

/-- A genuine smooth microlocal split with arbitrary-order error-amplitude
decay for each fixed parameter and normalized frequency in its error support.
The existential constant is deliberately inside those parameter quantifiers. -/
theorem Family.exists_microlocal_error_pointwise_decay {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) :
    ∃ (δ : ℝ) (β : ℝ → ℝ), 0 < δ ∧ δ ≤ 1 / 4 ∧ ContDiff ℝ ∞ β ∧
      (∀ s, |s| ≤ δ / 2 → β s = 0) ∧ (∀ s, δ ≤ |s| → β s = 1) ∧
      HasCompactSupport (fun ξ : Plane => L.bandSymbol 0 ξ * (1 - β ξ.2)) ∧
      ∀ ξ ∈ tsupport (fun ξ : Plane => L.bandSymbol 0 ξ * (1 - β ξ.2)),
        ∀ (q : Parameters 2 d) (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, r ≠ 0 →
          ‖G.cutoffOscillatoryAmplitude χ q (r • ξ)‖ ≤ C * (|r|⁻¹) ^ n := by
  obtain ⟨δ, β, hδ, hδle, hβ, _, hβzero, hβone, _, herror, _, hnonstat⟩ :=
    G.exists_microlocal_band_split χ hc hγ L
  refine ⟨δ, β, hδ, hδle, hβ, hβzero, hβone, herror, ?_⟩
  intro ξ hξ q n
  exact G.cutoffOscillatoryAmplitude_errorSymbol_decay χ hχ hc hγ _ hnonstat hξ q n

end PlanarNikodym
