import PlanarNikodym.Analysis.Fourier.GlyzFiberPatchTransport
import PlanarNikodym.Analysis.Fourier.CriticalMainLpDecay

/-! Compact unused-coordinate fibers lift the actual selected-plane
main term to the complete original parameter measure. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff BigOperators
namespace PlanarNikodym

def fullFiniteSliceMainMeasure (d N : ℕ) : Measure (Fin N × Parameters 2 d) :=
  Measure.count.prod volume

instance fullFiniteSliceMainMeasure_sfinite (d N : ℕ) :
    SFinite (fullFiniteSliceMainMeasure d N) := by
  unfold fullFiniteSliceMainMeasure
  infer_instance

def Family.fullFiniteSliceMain {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (r b δ : ℝ) (N : ℕ)
    (f : Plane → ℂ) (w : Fin N × Parameters 2 d) : ℂ :=
  G.cutoffPartialExtension (scaleTimeLocalizedCutoff χ b δ w.1.val) L β r f w.2

theorem Family.measurable_fullFiniteSliceMain {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (ha : ∀ x ∈ tsupport χ, AnalyticAt ℝ (fun x => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : Continuous β)
    (r b δ : ℝ) (N : ℕ) {f : Plane → ℂ} (hf : Integrable f) :
    Measurable (G.fullFiniteSliceMain χ L β r b δ N f) := by
  apply measurable_from_prod_countable_right
  intro j
  exact (G.stronglyMeasurable_cutoffPartialExtension _
    (hχ.mul ((contDiff_scaleTimeCutoff b δ j.val).continuous.comp continuous_fst))
    (hasCompactSupport_scaleTimeLocalizedCutoff hc b δ j.val)
    (fun x hx => ha x (tsupport_scaleTimeLocalizedCutoff_subset χ b δ j.val hx))
    L hβ hf r).measurable

theorem full_finite_lintegral_fibers {d N : ℕ}
    (σ : Fin 2 ↪ Fin (d + 2)) (v : Aux (d + 2))
    (H : Fin N × Parameters 2 d → ℂ) (hH : Measurable H) (p : ℝ) :
    (∫⁻ w, ‖H w‖ₑ ^ p ∂fullFiniteSliceMainMeasure d N) =
      ∫⁻ u : UnselectedCoordinates σ, ∫⁻ w : Fin N × Aux 2,
        ‖H (w.1, glyzFiberParameter σ v u w.2)‖ₑ ^ p ∂finiteSliceMainMeasure N := by
  have hj (j : Fin N) : Measurable (fun x => ‖H (j, x)‖ₑ ^ p) :=
    (hH.comp (measurable_const.prodMk measurable_id)).enorm.pow_const p
  have hf (j : Fin N) : Measurable (fun u : UnselectedCoordinates σ =>
      ∫⁻ z : Aux 2, ‖H (j, glyzFiberParameter σ v u z)‖ₑ ^ p) := by
    have hh : Measurable (fun uz : UnselectedCoordinates σ × Aux 2 =>
        ‖H (j, glyzFiberParameter σ v uz.1 uz.2)‖ₑ ^ p) :=
      (hj j).comp (continuous_glyzFiberParameter σ v).measurable
    exact hh.lintegral_prod_right
  have hu (u : UnselectedCoordinates σ) : Measurable
      (fun w : Fin N × Aux 2 => ‖H (w.1, glyzFiberParameter σ v u w.2)‖ₑ ^ p) := by
    apply measurable_from_prod_countable_right
    intro j
    exact (hj j).comp ((continuous_glyzFiberParameter σ v).comp
      (continuous_const.prodMk continuous_id)).measurable
  rw [fullFiniteSliceMainMeasure, lintegral_prod _ (hH.enorm.pow_const p).aemeasurable,
    lintegral_count, tsum_fintype]
  simp_rw [glyz_lintegral_original_fibers σ v _ (hj _)]
  rw [← lintegral_finsetSum Finset.univ (fun j _ => hf j)]
  apply lintegral_congr
  intro u
  rw [finiteSliceMainMeasure, lintegral_prod _ (hu u).aemeasurable,
    lintegral_count, tsum_fintype]

/-- The compact-volume coefficient is fixed before the number of time
pieces, the actual functions and their common fiber norm bound. -/
theorem exists_full_finite_fiber_norm_factor {d : ℕ}
    (σ : Fin 2 ↪ Fin (d + 2)) (v : Aux (d + 2))
    (K : Set (ℝ × Parameters 2 d)) (hK : IsCompact K) :
    ∃ V : ℝ, 0 < V ∧ ∀ (N : ℕ) (H : Fin N × Parameters 2 d → ℂ),
      Measurable H → (∀ w, H w ≠ 0 → ∃ t, (t, w.2) ∈ K) →
      ∀ (p : ℝ≥0), 0 < p → ∀ A : ℝ≥0∞,
      (∀ u : UnselectedCoordinates σ,
        eLpNorm (fun w : Fin N × Aux 2 => H (w.1, glyzFiberParameter σ v u w.2))
          p (finiteSliceMainMeasure N) ≤ A) →
      eLpNorm H p (fullFiniteSliceMainMeasure d N) ≤
        ENNReal.ofReal (V ^ (1 / (p : ℝ))) * A := by
  classical
  let U := glyzFiberProjection σ v '' K
  have hU : IsCompact U := hK.image (continuous_glyzFiberProjection σ v)
  let V := (volume U).toReal + 1
  have hV : 0 < V := by dsimp [V]; positivity
  have hUV : volume U ≤ ENNReal.ofReal V := by
    rw [← ENNReal.ofReal_toReal hU.measure_lt_top.ne]
    exact ENNReal.ofReal_le_ofReal (by dsimp only [V]; linarith)
  refine ⟨V, hV, ?_⟩
  intro N H hH hs p hp A hb
  have hpR : 0 < (p : ℝ) := hp
  let E := fun u : UnselectedCoordinates σ => ∫⁻ w : Fin N × Aux 2,
    ‖H (w.1, glyzFiberParameter σ v u w.2)‖ₑ ^ (p : ℝ) ∂finiteSliceMainMeasure N
  have hEs : Function.support E ⊆ U := by
    intro u hu
    by_contra hnot
    have hz (w : Fin N × Aux 2) : H (w.1, glyzFiberParameter σ v u w.2) = 0 := by
      by_contra hne
      obtain ⟨t, ht⟩ := hs _ hne
      exact hnot ⟨_, ht, glyzFiberProjection_fiber σ v t u w.2⟩
    apply hu
    simp only [E, hz, enorm_zero, ENNReal.zero_rpow_of_pos hpR, lintegral_zero]
  have hEp (u : UnselectedCoordinates σ) : E u ≤ A ^ (p : ℝ) := by
    dsimp only [E]
    rw [← eLpNorm_nnreal_pow_eq_lintegral hp.ne']
    exact ENNReal.rpow_le_rpow (hb u) hpR.le
  have hint : (∫⁻ w, ‖H w‖ₑ ^ (p : ℝ) ∂fullFiniteSliceMainMeasure d N) ≤
      ENNReal.ofReal V * A ^ (p : ℝ) := by
    rw [full_finite_lintegral_fibers σ v H hH]
    change (∫⁻ u, E u) ≤ _
    rw [← setLIntegral_eq_of_support_subset hEs]
    calc
      _ ≤ ∫⁻ _u in U, A ^ (p : ℝ) := lintegral_mono hEp
      _ = volume U * A ^ (p : ℝ) := by rw [setLIntegral_const, mul_comm]
      _ ≤ _ := mul_le_mul_left hUV _
  rw [eLpNorm_nnreal_eq_lintegral hp.ne']
  calc
    _ ≤ (ENNReal.ofReal V * A ^ (p : ℝ)) ^ (1 / (p : ℝ)) :=
      ENNReal.rpow_le_rpow hint (by positivity)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
        mul_one_div_cancel hpR.ne', ENNReal.rpow_one,
        ← ENNReal.ofReal_rpow_of_nonneg hV.le (by positivity)]

/-- Main pieces vanish outside the original cutoff's parameter projection. -/
theorem Family.fullFiniteSliceMain_support {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (L : FrequencyCutoff) (β : ℝ → ℝ) (r b δ : ℝ) (N : ℕ)
    (f : Plane → ℂ) (w : Fin N × Parameters 2 d)
    (hw : G.fullFiniteSliceMain χ L β r b δ N f w ≠ 0) :
    ∃ t, (t, w.2) ∈ tsupport χ := by
  by_contra hn
  have hz : ∀ t, χ (t, w.2) = 0 := by
    intro t
    by_contra ht
    exact hn ⟨t, subset_tsupport χ ht⟩
  apply hw
  simp only [Family.fullFiniteSliceMain, Family.cutoffPartialExtension,
    scaleTimeLocalizedCutoff, hz, zero_mul, Complex.ofReal_zero, integral_zero, smul_zero]

end PlanarNikodym
