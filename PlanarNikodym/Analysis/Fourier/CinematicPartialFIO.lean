import PlanarNikodym.Analysis.Maximal.FullCinematicFIO
import PlanarNikodym.Analysis.Fourier.PartialDataRawExtension

/-! Exact full-FIO representation for the actual compact-symbol partial
Fourier main term. Continuity is proved for general integrable original
inputs; no Schwartz hypothesis or unweighted transform is substituted. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace PlanarNikodym

theorem continuous_partialFourierData_of_compact {a : Plane → ℂ}
    (ha : Continuous a) (hc : HasCompactSupport a) (r : ℝ) :
    Continuous (fun x : Plane => partialFourierData a r x.1 x.2) := by
  let F : Plane → ℝ → ℂ := fun x ξ => a (ξ,x.2) * oneDimFourierCharacter r x.1 ξ
  have hF : Continuous (Function.uncurry F) := by
    apply (ha.comp (continuous_snd.prodMk continuous_fst.snd)).mul
    unfold oneDimFourierCharacter
    fun_prop
  rw [← continuousOn_univ]
  exact continuousOn_integral_of_compact_support (hc.isCompact.image continuous_fst)
    hF.continuousOn (by
      intro x ξ _ hξ
      have hz : a (ξ,x.2) = 0 := image_eq_zero_of_notMem_tsupport
        (fun hh => hξ ⟨(ξ,x.2),hh,rfl⟩)
      simp [hz])

theorem continuous_weightedPartialFourierData {m : Plane → ℝ}
    (hm : Continuous m) (hc : HasCompactSupport m) {f : Plane → ℂ}
    (hf : Integrable f) (r : ℝ) :
    Continuous (fun x : Plane => weightedPartialFourierData m f r x.1 x.2) :=
  continuous_partialFourierData_of_compact (weighted_scaledFourierData_continuous hm hf r)
    ((hc.comp_left (g := Complex.ofRealCLM) rfl).mul_right) r

theorem partialDataAmplitude_tsupport_subset {d : ℕ} (χ : Cutoff d) (ρ : ℝ → ℝ) :
    tsupport (partialDataAmplitude χ ρ) ⊆
      {z | (z.2.1,z.1) ∈ tsupport χ ∧ z.2.2 ∈ tsupport ρ} := by
  intro z hz
  have hleft : tsupport (partialDataAmplitude χ ρ) ⊆
      tsupport (fun z : Parameters 2 d × Plane => (χ (z.2.1,z.1) : ℂ)) :=
    tsupport_mul_subset_left
  have hright : tsupport (partialDataAmplitude χ ρ) ⊆
      tsupport (fun z : Parameters 2 d × Plane => (ρ z.2.2 : ℂ)) :=
    tsupport_mul_subset_right
  constructor
  · have hh := tsupport_comp_subset_preimage (fun x => (χ x : ℂ))
      (continuous_snd.fst.prodMk continuous_fst) (hleft hz)
    exact tsupport_comp_subset (g := Complex.ofRealCLM) rfl χ hh
  · have hh := tsupport_comp_subset_preimage (fun η => (ρ η : ℂ))
      continuous_snd.snd (hright hz)
    exact tsupport_comp_subset (g := Complex.ofRealCLM) rfl ρ hh

theorem Family.cutoffPartialExtension_eq_fullFIO {d : ℕ}
    (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hρ1 : ∀ η ∈ Prod.snd '' tsupport (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2), ρ η = 1)
    (r : ℝ) {f : Plane → ℂ} (hf : Integrable f) (q : Parameters 2 d) :
    G.cutoffPartialExtension χ L β r f q = r^2 •
      e2FullFIOIntegral (2*Real.pi*r) (fun q x => x.2 * G.γ x.1 q)
        (partialDataAmplitude χ ρ)
        (fun x => weightedPartialFourierData (fun ξ => L.bandSymbol 0 ξ * β ξ.2)
          f r x.1 x.2) q := by
  let m : Plane → ℝ := fun ξ => L.bandSymbol 0 ξ * β ξ.2
  have hm : ContDiff ℝ ∞ m := (L.bandSymbol_smooth 0).mul (hβ.comp contDiff_snd)
  have hmc : HasCompactSupport m := (L.bandSymbol_compact 0).mul_right
  have hg := continuous_weightedPartialFourierData hm.continuous hmc hf r
  have hΦ : Continuous (fun z : Parameters 2 d × Plane => z.2.2 * G.γ z.2.1 z.1) :=
    continuous_snd.snd.mul (hG.continuous.comp (continuous_snd.fst.prodMk continuous_fst))
  have hi := integrable_fullFIO_input_of_continuous hΦ
    (contDiff_partialDataAmplitude hχ hρ).continuous
    (hasCompactSupport_partialDataAmplitude hc hcρ) hg (2*Real.pi*r) q
  unfold e2FullFIOIntegral
  rw [Measure.volume_eq_prod,integral_prod_symm _ hi]
  unfold Family.cutoffPartialExtension
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases hη : η ∈ Prod.snd '' tsupport m
  · simp only [e2FIOAmplitudeKernel,partialDataAmplitude,hρ1 η hη,
      Complex.ofReal_one,mul_one,oneDimFourierCharacter]
    have he : 2*Real.pi*r*(η*G.γ t q) = 2*Real.pi*r*G.γ t q*η := by ring
    rw [he]
    ring
  · rw [weightedPartialFourierData_eq_zero_of_vertical r t η hη]
    simp

end PlanarNikodym
