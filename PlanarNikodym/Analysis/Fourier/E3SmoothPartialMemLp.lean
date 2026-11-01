import PlanarNikodym.Analysis.Fourier.GlyzPartialExtensionMemLp
import PlanarNikodym.Analysis.Fourier.E3SmoothPartialDecouplingTransfer

/-! Finiteness of the actual partial extension for C∞ phases. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff
namespace PlanarNikodym

set_option maxHeartbeats 800000 in
theorem Family.e3_memLp_cutoffPartialExtension {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β)
    {f : Plane → ℂ} (hf : Integrable f) (r : ℝ) (p : ℝ≥0∞) :
    MemLp (G.cutoffPartialExtension χ L β r f) p volume := by
  let m : Plane → ℝ := fun ξ => L.bandSymbol 0 ξ * β ξ.2
  have hm : Continuous m := (L.bandSymbol_smooth 0).continuous.mul (hβ.continuous.comp continuous_snd)
  have hmc : HasCompactSupport m := (L.bandSymbol_compact 0).mul_right
  obtain ⟨ρ, hρs, hρc, hρ⟩ := exists_partialData_radial_cutoff hmc
  let T := Prod.fst '' tsupport χ
  have hTc : IsCompact T := hc.isCompact.image continuous_fst
  have hT : ∀ x ∈ tsupport χ, x.1 ∈ T := fun x hx => ⟨x, hx, rfl⟩
  let g := timeRestrictedPartialData T m f r
  have hg : Integrable g := integrable_timeRestrictedPartialData hTc.measurableSet
    hTc.measure_lt_top.ne hm hmc hf r
  let a := partialDataAmplitude χ ρ
  have ha' : ContDiff ℝ ∞ a := contDiff_partialDataAmplitude hχ hρs
  have hac : HasCompactSupport a := hasCompactSupport_partialDataAmplitude hc hρc
  have hΦH : ContDiff ℝ ∞ (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) :=
    hG.comp (contDiff_snd.prodMk contDiff_fst)
  have hraw := memLp_glyzRawExtension volume hΦH ha' hac hg (2 * Real.pi * r) p
  have hparent : G.cutoffPartialExtension χ L β r f =
      r ^ 2 • glyzRawExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) a g
        (2 * Real.pi * r) := by
    funext x
    exact G.cutoffPartialExtension_eq_raw_compact_amplitude χ L β T hT ρ hρ r f x
  rw [hparent]
  exact hraw.const_smul _

end PlanarNikodym
