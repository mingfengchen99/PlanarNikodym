import PlanarNikodym.Analysis.Fourier.UniformTimeSliceSquareSum
import PlanarNikodym.Analysis.Fourier.PartialExtensionL2Prefactor

/-! The actual microlocal main pieces, including their true `r²`
prefactor.  The compact-symbol bound and uniform slice constant are
constructed before all frequency, partition, chart-fibre and input
choices. Their resulting squared L² decay is exactly `r⁻¹`. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace PlanarNikodym

theorem partialExtension_L2_frequency_cancel {r : ℝ} (hr : r ≠ 0) (C M κ : ℝ) :
    r ^ (4 : ℕ) * (C ^ (2 : ℕ) * κ⁻¹ * r⁻¹ ^ (2 : ℕ)) *
      (M ^ (2 : ℕ) * r⁻¹ ^ (3 : ℕ)) =
        C ^ (2 : ℕ) * M ^ (2 : ℕ) * κ⁻¹ * r⁻¹ := by
  field_simp

/-- The original compact-symbol main operator has a genuine uniform
square-sum estimate.  The data are the original L¹∩L² function, and the
time window occurs only once in the actual amplitude. -/
theorem Family.exists_uniform_cutoffPartialExtension_square_sum_bound
    {d : ℕ} (G : Family 2 d)
    (E : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux 2)
      ((ℝ × Aux (d + 2)) × Aux 2))
    (hi : AnalyticOnNhd ℝ E.symm E.target) (σ : Fin 2 ↪ Fin (d + 2))
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (F : FrequencyCutoff) (βfreq : ℝ → ℝ) (hβfreq : Continuous βfreq)
    {L U : Set (Parameters 2 d × ℝ)} (hL : IsCompact L) (hU : IsOpen U)
    (hLU : L ⊆ U)
    (hΦ : ∀ x ∈ U, ContDiffAt ℝ ∞ (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) x)
    {T : Set ((ℝ × Aux (d + 2)) × Aux 2)} (hT : IsCompact T) (hTE : T ⊆ E.target) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧
      (∀ ξ : Plane, |F.bandSymbol 0 ξ * βfreq ξ.2| ≤ M) ∧
      ∀ (b δ : ℝ) (N : ℕ) (v : ℕ → Aux (d + 2))
      (e : ℕ → OpenPartialHomeomorph (Aux 2) (Aux 2)) (K : ℕ → Set (Aux 2))
      (hm : 2 ≤ d + 2) (β : ℝ), 0 ≤ β →
      TimeSliceChartGeometry G E σ (fun x => (χ (x.2.1, x.1) : ℂ))
        L T b δ N β v e K hm →
      ∀ f : Plane → ℂ, Integrable f → MemLp f 2 volume →
      ∀ κ r : ℝ, 0 < κ → 0 < r → 0 < δ → δ ≤ 1 →
      (2 * Real.pi * r) * δ ^ (2 : ℕ) ∈ Icc (0 : ℝ) 1 →
      (∀ ξ : Plane, |ξ.2| < κ → F.bandSymbol 0 ξ * βfreq ξ.2 = 0) →
      ENNReal.ofReal β * (∑ i ∈ Finset.range N, ∫⁻ z in K i,
        ‖G.cutoffPartialExtension (scaleTimeLocalizedCutoff χ b δ i) F βfreq r f
          (parameterFrame d (v i + coordinateInsertion σ z))‖ₑ ^ (2 : ℕ)) ≤
        (3 : ℝ≥0∞) * ENNReal.ofReal (C ^ (2 : ℕ) * M ^ (2 : ℕ) * κ⁻¹ * r⁻¹) *
          ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ) := by
  let m : Plane → ℝ := fun ξ => F.bandSymbol 0 ξ * βfreq ξ.2
  have hm : Continuous m := (F.bandSymbol_smooth 0).continuous.mul
    (hβfreq.comp continuous_snd)
  have hmc : HasCompactSupport m := (F.bandSymbol_compact 0).mul_right
  obtain ⟨ξ₀, hmax⟩ := hm.norm.exists_forall_ge_of_hasCompactSupport hmc.norm
  let M : ℝ := ‖m ξ₀‖
  have hM : 0 ≤ M := norm_nonneg _
  have hbound : ∀ ξ : Plane, |m ξ| ≤ M := by
    intro ξ
    simpa only [M, Real.norm_eq_abs] using hmax ξ
  have ha : ContDiff ℝ ∞ (fun x : Parameters 2 d × ℝ × ℝ => (χ (x.2.1, x.1) : ℂ)) := by
    apply Complex.ofRealCLM.contDiff.comp
    exact hχ.comp (by fun_prop)
  obtain ⟨C, hC, hsum⟩ := G.exists_uniform_weighted_timeSlice_square_sum_bound
    E hi σ (fun x => (χ (x.2.1, x.1) : ℂ)) ha hL hU hLU hΦ hT hTE hm hmc
  refine ⟨C, M, hC, hM, hbound, ?_⟩
  intro b δ N v e K hd β hβ hgeom f h1 h2 κ r hκ hr hδ hδ1 hα hgap
  have hs := hsum b δ N v e K hd β M hβ hgeom hbound f h1 h2 κ r hκ hr hδ hδ1 hα hgap
  rw [G.sum_lintegral_cutoffPartialExtension_scaleTimeLocalized_sq
    χ F βfreq r b hδ.ne' N f σ v K]
  calc
    _ = ENNReal.ofReal (r ^ (4 : ℕ)) * (ENNReal.ofReal β * _ ) := by
      dsimp only [m]
      ac_rfl
    _ ≤ ENNReal.ofReal (r ^ (4 : ℕ)) *
        ((3 : ℝ≥0∞) * ENNReal.ofReal (C ^ (2 : ℕ) * κ⁻¹ * r⁻¹ ^ (2 : ℕ)) *
          (ENNReal.ofReal (M ^ (2 : ℕ) * r⁻¹ ^ (3 : ℕ)) *
            ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ))) := mul_le_mul_right hs _
    _ = _ := by
      calc
        _ = (3 : ℝ≥0∞) *
            (ENNReal.ofReal (r ^ (4 : ℕ)) *
              ENNReal.ofReal (C ^ (2 : ℕ) * κ⁻¹ * r⁻¹ ^ (2 : ℕ)) *
                ENNReal.ofReal (M ^ (2 : ℕ) * r⁻¹ ^ (3 : ℕ))) *
                  ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ) := by ac_rfl
        _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ r ^ (4 : ℕ)),
            ← ENNReal.ofReal_mul (by positivity :
              0 ≤ r ^ (4 : ℕ) * (C ^ (2 : ℕ) * κ⁻¹ * r⁻¹ ^ (2 : ℕ))),
            partialExtension_L2_frequency_cancel hr.ne']

end PlanarNikodym
