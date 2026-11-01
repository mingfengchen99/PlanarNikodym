import PlanarNikodym.Analysis.Fourier.LocalizedPartialDataMass
import PlanarNikodym.Analysis.Fourier.GlyzRawKernel

/-! Exact compact-amplitude raw-extension representation of the original
partial Fourier main term and its smooth time pieces. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal NNReal ContDiff
namespace PlanarNikodym

def partialDataAmplitude {d : ℕ} (χ : Cutoff d) (ρ : ℝ → ℝ) :
    Parameters 2 d × Plane → ℂ :=
  fun x => (χ (x.2.1, x.1) : ℂ) * (ρ x.2.2 : ℂ)

theorem contDiff_partialDataAmplitude {d : ℕ} {χ : Cutoff d}
    (hχ : ContDiff ℝ ∞ χ) {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (partialDataAmplitude χ ρ) :=
  (Complex.ofRealCLM.contDiff.comp (hχ.comp (contDiff_snd.fst.prodMk contDiff_fst))).mul
    (Complex.ofRealCLM.contDiff.comp (hρ.comp contDiff_snd.snd))

theorem hasCompactSupport_partialDataAmplitude {d : ℕ} {χ : Cutoff d}
    (hcχ : HasCompactSupport χ) {ρ : ℝ → ℝ} (hcρ : HasCompactSupport ρ) :
    HasCompactSupport (partialDataAmplitude χ ρ) := by
  apply HasCompactSupport.intro ((hcχ.prod hcρ).image
    (continuous_fst.snd.prodMk (continuous_fst.fst.prodMk continuous_snd)))
  intro x hx
  have hnot : χ (x.2.1, x.1) = 0 ∨ ρ x.2.2 = 0 := by
    by_contra hh
    push Not at hh
    exact hx ⟨((x.2.1, x.1), x.2.2),
      ⟨subset_tsupport _ hh.1, subset_tsupport _ hh.2⟩, rfl⟩
  rcases hnot with h | h <;> simp [partialDataAmplitude, h]

theorem exists_partialData_radial_cutoff {m : Plane → ℝ} (hc : HasCompactSupport m) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
      (∀ η ∈ Prod.snd '' tsupport m, ρ η = 1) := by
  obtain ⟨R, hR, hb⟩ := (hc.isCompact.image continuous_snd).isBounded.exists_pos_norm_le
  let b : ContDiffBump (0 : ℝ) := ⟨R, R + 1, hR, by linarith⟩
  refine ⟨b, b.contDiff, b.hasCompactSupport, ?_⟩
  intro η hη
  exact b.one_of_mem_closedBall (by simpa only [mem_closedBall, dist_zero_right] using hb η hη)

theorem Family.cutoffPartialExtension_eq_raw_compact_amplitude {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (L : FrequencyCutoff) (β : ℝ → ℝ)
    (T : Set ℝ) (hT : ∀ x ∈ tsupport χ, x.1 ∈ T)
    (ρ : ℝ → ℝ)
    (hρ : ∀ η ∈ Prod.snd '' tsupport (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2), ρ η = 1)
    (r : ℝ) (f : Plane → ℂ) (q : Parameters 2 d) :
    G.cutoffPartialExtension χ L β r f q =
      r ^ 2 • glyzRawExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1)
        (partialDataAmplitude χ ρ)
        (timeRestrictedPartialData T (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2) f r)
        (2 * Real.pi * r) q := by
  unfold Family.cutoffPartialExtension glyzRawExtension
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases hχ : χ (t, q) = 0
  · simp [partialDataAmplitude, hχ]
  have ht : t ∈ T := hT (t, q) (subset_tsupport _ hχ)
  have hid : timeRestrictedPartialData T (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2) f r (t, η) =
      weightedPartialFourierData (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2) f r t η :=
    indicator_of_mem (show (t, η) ∈ T ×ˢ (univ : Set ℝ) from ⟨ht, mem_univ _⟩) _
  rw [hid]
  by_cases hη : η ∈ Prod.snd '' tsupport (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2)
  · simp only [partialDataAmplitude, hρ η hη, Complex.ofReal_one, mul_one,
      phaseOscillation, oneDimFourierCharacter]
    have he : (2 * Real.pi * r * η * G.γ t q : ℝ) = 2 * Real.pi * r * G.γ t q * η := by ring
    rw [he]
    ring
  · rw [weightedPartialFourierData_eq_zero_of_vertical r t η hη]
    simp

theorem Family.cutoffPartialExtension_timeSlice_compact_amplitude {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (L : FrequencyCutoff) (β : ℝ → ℝ)
    (T : Set ℝ) (hT : ∀ x ∈ tsupport χ, x.1 ∈ T)
    (ρ : ℝ → ℝ)
    (hρ : ∀ η ∈ Prod.snd '' tsupport (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2), ρ η = 1)
    (r c δ : ℝ) (f : Plane → ℂ) (q : Parameters 2 d) :
    G.cutoffPartialExtension (fun x => χ x * timePartitionWindow ((x.1 - c) / δ)) L β r f q =
      r ^ 2 • timeSliceExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1)
        (partialDataAmplitude χ ρ)
        (timeRestrictedPartialData T (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2) f r)
        (2 * Real.pi * r) c δ q := by
  have ht : ∀ x ∈ tsupport (fun x => χ x * timePartitionWindow ((x.1 - c) / δ)), x.1 ∈ T :=
    fun x hx => hT x (tsupport_mul_subset_left hx)
  rw [G.cutoffPartialExtension_eq_raw_compact_amplitude _ L β T ht ρ hρ]
  unfold glyzRawExtension timeSliceExtension
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [partialDataAmplitude, Complex.ofReal_mul]
  ring

end PlanarNikodym
