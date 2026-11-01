import PlanarNikodym.Analysis.Fourier.PhysicalKernelTails
import PlanarNikodym.Analysis.Fourier.CompactAveragePointwiseBound

/-! A fixed physical cutoff reduces the scalar smoothing problem to
compactly supported inputs. The cutoff is chosen before all exponents,
frequencies, and inputs, and the discarded term has arbitrary decay. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal NNReal ContDiff
namespace PlanarNikodym

theorem Family.exists_compact_graph_norm_bound {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x) :
    ∃ R : ℝ, 0 < R ∧ ∀ x ∈ tsupport χ, ‖G.graphMap x.2 x.1‖ ≤ R := by
  have hcont : ContinuousOn (fun x : ℝ × Parameters 2 d => G.graphMap x.2 x.1)
      (tsupport χ) := by
    exact continuousOn_fst.prodMk (fun x hx => (hγ x hx).continuousWithinAt)
  obtain ⟨R, hR, hb⟩ := (hc.isCompact.image_of_continuousOn hcont).isBounded.exists_pos_norm_le
  exact ⟨R, hR, fun x hx => hb _ ⟨x, hx, rfl⟩⟩

theorem Family.exists_physical_input_localization {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    {m : Plane → ℝ} (hm : ContDiff ℝ ∞ m) (hcm : HasCompactSupport m) :
    ∃ R : ℝ, 0 < R ∧ ∀ p : ℝ≥0∞, 1 ≤ p → ∀ N : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ f : Plane → ℂ, Integrable f →
        eLpNorm (G.cutoffAverage χ (scaledFrequencyConvolution m r
          ((closedBall (0 : Plane) R)ᶜ.indicator f))) p volume ≤
            ENNReal.ofReal (C * (r⁻¹) ^ N) * eLpNorm f p volume := by
  classical
  obtain ⟨S, hS, hgraph⟩ := G.exists_compact_graph_norm_bound χ hc hγ
  refine ⟨S + 1, by linarith, ?_⟩
  intro p hp N
  let q : ℝ≥0∞ := (1 - p⁻¹)⁻¹
  letI : ENNReal.HolderConjugate q p := by
    rw [ENNReal.holderConjugate_iff]
    dsimp only [q]
    rw [inv_inv]
    exact tsub_add_cancel_of_le (by simpa using ENNReal.inv_le_inv.mpr hp)
  obtain ⟨B, hB, hfar⟩ := exists_scaledFrequencyConvolution_far_enorm_bound hm hcm p q N
  obtain ⟨A, hA, havg⟩ := G.exists_cutoffAverage_Lp_of_graph_bound χ hχ hc p
  refine ⟨A * B, mul_nonneg hA hB, ?_⟩
  intro r hr f hf
  let g := (closedBall (0 : Plane) (S + 1))ᶜ.indicator f
  have hg : Integrable g := hf.indicator measurableSet_closedBall.compl
  have hgnorm : eLpNorm g p volume ≤ eLpNorm f p volume := eLpNorm_indicator_le _
  have hbnd (x : ℝ × Parameters 2 d) (hx : x ∈ tsupport χ) :
      ‖scaledFrequencyConvolution m r g (G.graphMap x.2 x.1)‖ₑ ≤
        ENNReal.ofReal (B * (r⁻¹) ^ N) * eLpNorm f p volume := by
    have hs : ∀ y, g y ≠ 0 → 1 ≤ ‖G.graphMap x.2 x.1 - y‖ := by
      intro y hy
      have hyout : y ∉ closedBall (0 : Plane) (S + 1) := by
        by_contra hin
        exact hy (indicator_of_notMem (notMem_compl_iff.mpr hin) f)
      have hyn : S + 1 < ‖y‖ := by
        simpa only [mem_closedBall, dist_zero_right, not_le] using hyout
      have hnorm := norm_sub_norm_le y (G.graphMap x.2 x.1)
      rw [norm_sub_rev y] at hnorm
      linarith [hgraph x hx]
    exact (hfar r hr g hg _ hs).trans (mul_le_mul_right hgnorm _)
  have h := havg (scaledFrequencyConvolution m r g) (B * (r⁻¹) ^ N)
    (by positivity) (eLpNorm f p volume) hbnd
  simpa only [mul_assoc] using h

theorem Family.exists_partialExtension_physical_localization {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β) :
    ∃ R : ℝ, 0 < R ∧ ∀ p : ℝ≥0∞, 1 ≤ p → ∀ N : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ f : Plane → ℂ, Integrable f →
        eLpNorm (G.cutoffPartialExtension χ L β r
          ((closedBall (0 : Plane) R)ᶜ.indicator f)) p volume ≤
            ENNReal.ofReal (C * (r⁻¹) ^ N) * eLpNorm f p volume := by
  obtain ⟨R, hR, hb⟩ := G.exists_physical_input_localization χ hχ hc hγ
    ((L.bandSymbol_smooth 0).mul (hβ.comp contDiff_snd))
    (L.bandSymbol_compact 0).mul_right
  refine ⟨R, hR, ?_⟩
  intro p hp N
  obtain ⟨C, hC, hbound⟩ := hb p hp N
  refine ⟨C, hC, ?_⟩
  intro r hr f hf
  have he : G.cutoffPartialExtension χ L β r ((closedBall (0 : Plane) R)ᶜ.indicator f) =
      G.cutoffAverage χ (scaledFrequencyConvolution
        (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2) r
        ((closedBall (0 : Plane) R)ᶜ.indicator f)) := by
    funext q
    exact G.cutoffPartialExtension_eq_scaledFrequencyConvolution χ hχ hc hγ L β hβ.continuous
      (hf.indicator measurableSet_closedBall.compl) r q
  rw [he]
  exact hbound r hr f hf

end PlanarNikodym
