import PlanarNikodym.Analysis.Fourier.SmoothSmallCinematicMainLp
import PlanarNikodym.Analysis.Fourier.SmallCinematicMainL2Norm

/-! Genuine C-infinity estimates, including zero auxiliary dimension. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal NNReal BigOperators ComplexConjugate
namespace PlanarNikodym

theorem Family.exists_smooth_finite_cinematic_small_main_L2_norm_partition {d : ℕ}
    (G : Family 2 d) (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)

    (hdet : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (F : FrequencyCutoff) (βfreq : ℝ → ℝ) (hβfreq : Continuous βfreq) :
    ∃ (I : Finset (tsupport χ)) (ψ : I → Cutoff d)
      (σ : I → (Fin 2 ↪ Fin (d + 2))) (ε : ℝ),
      0 < ε ∧ (∀ x, ∑ i : I, ψ i x = χ x) ∧
      ∀ i : I, ContDiff ℝ ∞ (ψ i) ∧ HasCompactSupport (ψ i) ∧
        tsupport (ψ i) ⊆ tsupport χ ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ (b δ : ℝ) (N : ℕ) (u : UnselectedCoordinates (σ i))
          (f : Plane → ℂ), Integrable f → MemLp f 2 volume →
          ∀ κ r : ℝ, 0 < κ → 0 < r → 0 < δ → δ ≤ 1 → δ ≤ ε / 2 →
          (2 * Real.pi * r) * δ ^ (2 : ℕ) ∈ Icc (0 : ℝ) 1 →
          (∀ ξ : Plane, |ξ.2| < κ → F.bandSymbol 0 ξ * βfreq ξ.2 = 0) →
          eLpNorm (G.finiteSliceMain (ψ i) F βfreq r b δ N
            (fun z => parameterFrame d (((parameterFrame d).symm i.val.val.2 +
              selectedCoordinateSplit (σ i) (0, u)) + coordinateInsertion (σ i) z)) f)
            2 (finiteSliceMainMeasure N) ≤
            ENNReal.ofReal ((C * κ⁻¹ * r⁻¹) ^ (1 / (2 : ℝ))) * eLpNorm f 2 volume := by
  obtain ⟨I, ψ, σ, ε, hε, hsum, hpatch⟩ :=
    G.exists_e3_finite_cinematic_main_L2_partition hG χ hχ hc hχ0 hdet F βfreq hβfreq
  refine ⟨I, ψ, σ, ε, hε, hsum, ?_⟩
  intro i
  obtain ⟨hψ, hcψ, hsψ, β, C, M, hβ, hC, hM, _, hb⟩ := hpatch i
  let A := 3 * (C ^ 2 * M ^ 2) / β
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨hψ, hcψ, hsψ, A, hA, ?_⟩
  intro b δ N u f hf hf2 κ r hκ hr hδ hδ1 hδε hα hgap
  let q : Aux 2 → Parameters 2 d := fun z => parameterFrame d
    (((parameterFrame d).symm i.val.val.2 + selectedCoordinateSplit (σ i) (0, u)) +
      coordinateInsertion (σ i) z)
  have hq : Measurable q := by
    apply Continuous.measurable
    exact (parameterFrame d).continuous.comp
      (continuous_const.add (coordinateInsertion (σ i)).continuous)
  have hh := hb b δ N u f hf hf2 κ r hκ hr hδ hδ1 hδε hα hgap
  have hi := G.e3_lintegral_finiteSliceMain hG (ψ i) hψ.continuous hcψ F βfreq hβfreq r b δ N q hq hf (2 : ℝ)
  simp only [ENNReal.rpow_two] at hi
  change ENNReal.ofReal β * (∑ j ∈ Finset.range N, ∫⁻ z : Aux 2,
    ‖G.cutoffPartialExtension (scaleTimeLocalizedCutoff (ψ i) b δ j) F βfreq r f (q z)‖ₑ ^ (2 : ℕ)) ≤ _ at hh
  rw [← hi] at hh
  have hcoef : (ENNReal.ofReal β)⁻¹ *
      ((3 : ℝ≥0∞) * ENNReal.ofReal (C ^ 2 * M ^ 2 * κ⁻¹ * r⁻¹)) =
        ENNReal.ofReal (A * κ⁻¹ * r⁻¹) := by
    rw [← ENNReal.ofReal_inv_of_pos hβ]
    calc
      _ = ENNReal.ofReal (β⁻¹ * (3 * (C ^ 2 * M ^ 2 * κ⁻¹ * r⁻¹))) := by
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr hβ.le),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
        norm_num
      _ = _ := by congr 1; dsimp [A]; ring
  apply cinematic_main_L2_norm_of_square (finiteSliceMainMeasure N) volume _ f
    (mul_nonneg (mul_nonneg hA (inv_nonneg.mpr hκ.le)) (inv_nonneg.mpr hr.le))
  calc
    _ = (ENNReal.ofReal β)⁻¹ * (ENNReal.ofReal β *
        ∫⁻ w, ‖G.finiteSliceMain (ψ i) F βfreq r b δ N q f w‖ₑ ^ (2 : ℕ)
          ∂finiteSliceMainMeasure N) :=
      (ENNReal.inv_mul_cancel_left (ENNReal.ofReal_pos.mpr hβ).ne' ENNReal.ofReal_ne_top).symm
    _ ≤ (ENNReal.ofReal β)⁻¹ * ((3 : ℝ≥0∞) * ENNReal.ofReal
        (C ^ 2 * M ^ 2 * κ⁻¹ * r⁻¹) * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ)) :=
      mul_le_mul_right hh _
    _ = _ := by rw [← mul_assoc, hcoef]

end PlanarNikodym
