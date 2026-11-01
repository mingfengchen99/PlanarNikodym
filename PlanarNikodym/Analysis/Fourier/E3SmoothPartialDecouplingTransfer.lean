import PlanarNikodym.Analysis.Fourier.GlyzPartialDataBounds
import PlanarNikodym.Analysis.Fourier.GlyzFiniteFamilyLpNorm
import PlanarNikodym.Analysis.Fourier.GlyzCascadeDecoupling
import PlanarNikodym.Analysis.Fourier.FullCinematicMainLpTransport
import PlanarNikodym.Analysis.Fourier.E3SmoothPartialMeasurability

/-! Exact transfer of raw-extension decoupling to the original
partial Fourier main operator. The r^2 normalization is preserved. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal BigOperators ContDiff
namespace PlanarNikodym

set_option maxHeartbeats 1000000 in
theorem Family.e3_glyz_partial_decoupling_transfer {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hT : ∀ x ∈ tsupport χ, x.1 ∈ Icc (-1 : ℝ) 1)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β)
    (ρ : ℝ → ℝ) (hρs : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρ : ∀ η ∈ Prod.snd '' tsupport (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2), ρ η = 1)
    {p : ℝ≥0} (hp : 0 < p) {f : Plane → ℂ} (hf : Integrable f)
    (r : ℝ) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) {C α Q : ℝ}
    (hdec :
      let Φ := fun x : Parameters 2 d × ℝ => G.γ x.2 x.1
      let a := partialDataAmplitude χ ρ
      let g := timeRestrictedPartialData (Icc (-1 : ℝ) 1)
        (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2) f r
      lpNorm (glyzRawExtension Φ a g (2 * Real.pi * r)) p volume ≤
        C * (2 * Real.pi * r) ^ α *
          (∑ i : Fin N, lpNorm
            (timeSliceExtension Φ a g (2 * Real.pi * r) (-1 + (i : ℝ) * δ) δ)
              p volume ^ (p : ℝ)) ^ (1 / (p : ℝ)) +
        C * (2 * Real.pi * r) ^ (-Q) * (∫ y, ‖g y‖)) :
    lpNorm (G.cutoffPartialExtension χ L β r f) p volume ≤
      C * (2 * Real.pi * r) ^ α *
        lpNorm (G.fullFiniteSliceMain χ L β r (-1) δ N f) p (fullFiniteSliceMainMeasure d N) +
      C * r ^ 2 * (2 * Real.pi * r) ^ (-Q) *
        (∫ y, ‖timeRestrictedPartialData (Icc (-1 : ℝ) 1)
          (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2) f r y‖) := by
  let Φ := fun x : Parameters 2 d × ℝ => G.γ x.2 x.1
  let a := partialDataAmplitude χ ρ
  let m := fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2
  let g := timeRestrictedPartialData (Icc (-1 : ℝ) 1) m f r
  have hm : Continuous m := (L.bandSymbol_smooth 0).continuous.mul (hβ.continuous.comp continuous_snd)
  have hmc : HasCompactSupport m := (L.bandSymbol_compact 0).mul_right
  have hg : Integrable g := integrable_timeRestrictedPartialData measurableSet_Icc
    isCompact_Icc.measure_lt_top.ne hm hmc hf r
  have ha' : ContDiff ℝ ∞ a := contDiff_partialDataAmplitude hχ hρs
  have hac : HasCompactSupport a := hasCompactSupport_partialDataAmplitude hc hρc
  have hΦH : ContDiff ℝ ∞ (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) :=
    hG.comp (contDiff_snd.prodMk contDiff_fst)
  have hraw (u : Plane → ℂ) (hu : Integrable u) :
      MemLp (glyzRawExtension Φ a u (2 * Real.pi * r)) p volume := by
    exact memLp_glyzRawExtension volume hΦH ha' hac hu _ p
  let S := fun i : Fin N => timeSliceExtension Φ a g (2 * Real.pi * r) (-1 + (i : ℝ) * δ) δ
  have hS (i : Fin N) : MemLp (S i) p volume := by
    rw [show S i = glyzRawExtension Φ a (glyzExactTimePiece δ i g) (2 * Real.pi * r) from
      (glyzRawExtension_exactTimePiece_eq_timeSliceExtension Φ a g _ hδ i).symm]
    exact hraw _ (integrable_glyzExactTimePiece hg δ i)
  have hpiece (i : Fin N) :
      (fun x => G.fullFiniteSliceMain χ L β r (-1) δ N f (i, x)) = r ^ 2 • S i := by
    funext x
    have hcuteq : scaleTimeLocalizedCutoff χ (-1) δ i =
        fun z => χ z * timePartitionWindow ((z.1 - (-1 + (i : ℝ) * δ)) / δ) := by
      funext z
      unfold scaleTimeLocalizedCutoff scaleTimeCutoff
      congr 2
      field_simp [hδ.ne']
      ring
    change G.cutoffPartialExtension (scaleTimeLocalizedCutoff χ (-1) δ i) L β r f x = _
    rw [hcuteq, G.cutoffPartialExtension_timeSlice_compact_amplitude χ L β
      (Icc (-1 : ℝ) 1) hT ρ hρ]
    rfl
  have hp' (i : Fin N) :
      lpNorm (fun x => G.fullFiniteSliceMain χ L β r (-1) δ N f (i, x)) p volume =
        r ^ 2 * lpNorm (S i) p volume := by
    rw [hpiece, lpNorm_const_smul]
    simp [Real.norm_eq_abs]
  have hagg : lpNorm (G.fullFiniteSliceMain χ L β r (-1) δ N f) p
        (fullFiniteSliceMainMeasure d N) =
      r ^ 2 * (∑ i : Fin N, lpNorm (S i) p volume ^ (p : ℝ)) ^ (1 / (p : ℝ)) := by
    rw [fullFiniteSliceMainMeasure, glyz_finite_family_lpNorm volume N _
      (G.e3_measurable_fullFiniteSliceMain hG χ hχ.continuous hc L β hβ.continuous _ _ _ _ hf)
      hp (fun i => by rw [hpiece]; exact (hS i).const_smul _)]
    simp_rw [hp']
    exact glyz_finite_rpow_scalar N _ (fun _ => lpNorm_nonneg) (sq_nonneg r) hp
  have hparent : G.cutoffPartialExtension χ L β r f =
      r ^ 2 • glyzRawExtension Φ a g (2 * Real.pi * r) := by
    funext x
    exact G.cutoffPartialExtension_eq_raw_compact_amplitude χ L β
      (Icc (-1 : ℝ) 1) hT ρ hρ r f x
  rw [hparent, lpNorm_const_smul]
  have hscalar : ((‖r ^ 2‖₊ : ℝ≥0) : ℝ) = r ^ 2 := by
    simp [Real.norm_eq_abs]
  rw [hscalar]
  have hh := mul_le_mul_of_nonneg_left hdec (sq_nonneg r)
  calc
    _ ≤ r ^ 2 * (C * (2 * Real.pi * r) ^ α *
        (∑ i : Fin N, lpNorm (S i) p volume ^ (p : ℝ)) ^ (1 / (p : ℝ)) +
        C * (2 * Real.pi * r) ^ (-Q) * (∫ y, ‖g y‖)) := hh
    _ = _ := by rw [hagg]; ring

end PlanarNikodym
