import PlanarNikodym.Analysis.Fourier.MicrolocalErrorDecay
import PlanarNikodym.Analysis.Fourier.UniformNonstationaryPhase

/-! A uniform arbitrary-order decay bound for the actual microlocal error
symbol times the actual curve Fourier amplitude. Joint compactness provides
one constant for all curve parameters and normalized frequencies. This is
an amplitude bound, not a frequency-derivative or an Lp operator estimate. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace PlanarNikodym

def microlocalJointAmplitude {d : ℕ} (χ : Cutoff d) (m : Plane → ℝ)
    (x : (Parameters 2 d × Plane) × ℝ) : ℂ :=
  (χ (x.2, x.1.1) : ℂ) * (m x.1.2 : ℂ)

theorem microlocalJointAmplitude_tsupport_subset {d : ℕ} (χ : Cutoff d) (m : Plane → ℝ)
    {x : (Parameters 2 d × Plane) × ℝ} (hx : x ∈ tsupport (microlocalJointAmplitude χ m)) :
    (x.2, x.1.1) ∈ tsupport χ ∧ x.1.2 ∈ tsupport m := by
  have heχ : tsupport (fun y : (Parameters 2 d × Plane) × ℝ => (χ (y.2, y.1.1) : ℂ)) =
      tsupport (fun y : (Parameters 2 d × Plane) × ℝ => χ (y.2, y.1.1)) := by
    unfold tsupport
    congr 1
    ext y
    simp
  have hem : tsupport (fun y : (Parameters 2 d × Plane) × ℝ => (m y.1.2 : ℂ)) =
      tsupport (fun y : (Parameters 2 d × Plane) × ℝ => m y.1.2) := by
    unfold tsupport
    congr 1
    ext y
    simp
  constructor
  · exact tsupport_comp_subset_preimage χ (continuous_snd.prodMk continuous_fst.fst)
      (heχ ▸ tsupport_mul_subset_left hx)
  · exact tsupport_comp_subset_preimage m continuous_fst.snd
      (hem ▸ tsupport_mul_subset_right hx)

theorem contDiff_microlocalJointAmplitude {d : ℕ} {χ : Cutoff d} {m : Plane → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hm : ContDiff ℝ ∞ m) :
    ContDiff ℝ ∞ (microlocalJointAmplitude χ m) := by
  exact (Complex.ofRealCLM.contDiff.comp
    (hχ.comp (contDiff_snd.prodMk contDiff_fst.fst))).mul
      (Complex.ofRealCLM.contDiff.comp (hm.comp contDiff_fst.snd))

/-- Compactness of the joint amplitude follows from the actual compact
supports by a coordinate permutation, rather than a bounded-parameter input. -/
theorem hasCompactSupport_microlocalJointAmplitude {d : ℕ} {χ : Cutoff d} {m : Plane → ℝ}
    (hcχ : HasCompactSupport χ) (hcm : HasCompactSupport m) :
    HasCompactSupport (microlocalJointAmplitude χ m) := by
  let F : (ℝ × Parameters 2 d) × Plane → (Parameters 2 d × Plane) × ℝ :=
    fun y => ((y.1.2, y.2), y.1.1)
  have hF : Continuous F :=
    (continuous_fst.snd.prodMk continuous_snd).prodMk continuous_fst.fst
  let K := F '' (tsupport χ ×ˢ tsupport m)
  have hK : IsCompact K := (hcχ.isCompact.prod hcm.isCompact).image hF
  apply HasCompactSupport.intro hK
  intro x hx
  by_cases hχx : (x.2, x.1.1) ∈ tsupport χ
  · have hmx : x.1.2 ∉ tsupport m := by
      intro hmx
      exact hx ⟨((x.2, x.1.1), x.1.2), ⟨hχx, hmx⟩, rfl⟩
    simp only [microlocalJointAmplitude, image_eq_zero_of_notMem_tsupport hmx,
      Complex.ofReal_zero, mul_zero]
  · simp only [microlocalJointAmplitude, image_eq_zero_of_notMem_tsupport hχx,
      Complex.ofReal_zero, zero_mul]

/-- A real compact smooth frequency symbol supported in a nonstationary
region gives uniform error-amplitude decay in all parameters and frequencies. -/
theorem Family.exists_uniform_cutoffOscillatoryAmplitude_symbol_decay {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (m : Plane → ℝ) (hm : ContDiff ℝ ∞ m) (hcm : HasCompactSupport m)
    (hne : ∀ ξ ∈ tsupport m, ∀ x ∈ tsupport χ,
      deriv (G.graphPhase x.2 ξ) x.1 ≠ 0) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Parameters 2 d) (ξ : Plane) (r : ℝ), r ≠ 0 →
      ‖(m ξ : ℂ) * G.cutoffOscillatoryAmplitude χ q (r • ξ)‖ ≤ C * (|r|⁻¹) ^ n := by
  let a := microlocalJointAmplitude χ m
  let Φ : (Parameters 2 d × Plane) × ℝ → ℝ :=
    fun x => G.normalizedGraphPhase x.1.1 x.1.2 x.2
  have ha : ContDiff ℝ ∞ a := contDiff_microlocalJointAmplitude hχ hm
  have hca : HasCompactSupport a := hasCompactSupport_microlocalJointAmplitude hcχ hcm
  have hΦ : ∀ x ∈ tsupport a, ContDiffAt ℝ ∞ Φ x := by
    intro x hx
    obtain ⟨hxχ, _⟩ := microlocalJointAmplitude_tsupport_subset χ m hx
    have hg : ContDiffAt ℝ ∞
        (fun y : (Parameters 2 d × Plane) × ℝ => G.γ y.2 y.1.1) x :=
      (hγ (x.2, x.1.1) hxχ).comp x
        (f := fun y : (Parameters 2 d × Plane) × ℝ => (y.2, y.1.1))
        (contDiffAt_snd.prodMk contDiffAt_fst.fst)
    change ContDiffAt ℝ ∞ (fun y : (Parameters 2 d × Plane) × ℝ =>
      (2 * Real.pi) * (y.2 * y.1.2.1 + G.γ y.2 y.1.1 * y.1.2.2)) x
    exact contDiffAt_const.mul
      ((contDiffAt_snd.mul contDiffAt_fst.snd.fst).add (hg.mul contDiffAt_fst.snd.snd))
  have hΦne : ∀ x ∈ tsupport a, partialTimeDeriv Φ x ≠ 0 := by
    intro x hx
    obtain ⟨hxχ, hxm⟩ := microlocalJointAmplitude_tsupport_subset χ m hx
    have hp := (G.contDiffAt_graphPhase (hγ (x.2, x.1.1) hxχ) x.1.2).differentiableAt (by simp)
    change deriv (G.normalizedGraphPhase x.1.1 x.1.2) x.2 ≠ 0
    rw [show deriv (G.normalizedGraphPhase x.1.1 x.1.2) x.2 =
        (2 * Real.pi) * deriv (G.graphPhase x.1.1 x.1.2) x.2 from
      (hp.hasDerivAt.const_mul (2 * Real.pi)).deriv]
    exact mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero)
      (hne x.1.2 hxm (x.2, x.1.1) hxχ)
  obtain ⟨C, hC, hbound⟩ := exists_uniform_nonstationary_decay_constant hΦ ha hca hΦne n
  refine ⟨C, hC, ?_⟩
  intro q ξ r hr
  have he : (∫ t : ℝ, phaseOscillation (fun s => Φ ((q, ξ), s)) r t * a ((q, ξ), t)) =
      (m ξ : ℂ) * G.cutoffOscillatoryAmplitude χ q (r • ξ) := by
    rw [G.cutoffOscillatoryAmplitude_eq_phaseOscillation_integral χ q ξ r,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [Φ, a, microlocalJointAmplitude]
    ring
  rw [← he]
  exact hbound (q, ξ) r hr

/-- The smooth split is actually constructed from the compact cutoff
geometry, and its error has one decay constant for all curve parameters and
all normalized frequencies at each requested order. -/
theorem Family.exists_microlocal_error_uniform_decay {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) :
    ∃ (δ : ℝ) (β : ℝ → ℝ), 0 < δ ∧ δ ≤ 1 / 4 ∧ ContDiff ℝ ∞ β ∧
      (∀ s, |s| ≤ δ / 2 → β s = 0) ∧ (∀ s, δ ≤ |s| → β s = 1) ∧
      HasCompactSupport (fun ξ : Plane => L.bandSymbol 0 ξ * (1 - β ξ.2)) ∧
      ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Parameters 2 d) (ξ : Plane) (r : ℝ), r ≠ 0 →
        ‖((L.bandSymbol 0 ξ * (1 - β ξ.2) : ℝ) : ℂ) *
            G.cutoffOscillatoryAmplitude χ q (r • ξ)‖ ≤ C * (|r|⁻¹) ^ n := by
  obtain ⟨δ, β, hδ, hδle, hβ, _, hβzero, hβone, _, herror, _, hnonstat⟩ :=
    G.exists_microlocal_band_split χ hcχ hγ L
  refine ⟨δ, β, hδ, hδle, hβ, hβzero, hβone, herror, ?_⟩
  intro n
  apply G.exists_uniform_cutoffOscillatoryAmplitude_symbol_decay χ hχ hcχ hγ _
    ((L.bandSymbol_smooth 0).mul (contDiff_const.sub (hβ.comp contDiff_snd))) herror _ n
  intro ξ hξ x hx
  have h := hnonstat ξ hξ x hx
  intro hz
  simp only [hz, abs_zero] at h
  linarith

end PlanarNikodym
