import PlanarNikodym.Analysis.Fourier.FiniteSliceMainEndpoints
import PlanarNikodym.Analysis.Fourier.EndpointInterpolation
import Mathlib.MeasureTheory.Function.L2Space

/-! Actual Lp estimates at every sufficiently small time scale. The finite cinematic partition,
L² square sums and L∞ endpoint are all constructed, then interpolated on
the product of counting measure and the selected-parameter plane. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff
namespace PlanarNikodym

private theorem enorm_sq_eq_ofReal_norm_sq (z : ℂ) :
    ‖z‖ₑ ^ (2 : ℕ) = ENNReal.ofReal (‖z‖ ^ (2 : ℕ)) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]

/-- A real cinematic cutoff constructs a finite partition with uniform
Lp bounds for every finite family of actual time pieces satisfying rδ²≤1.
The scale factor is `(κ⁻¹ r⁻¹ δ^(p-2))^(1/p)`, with no loss depending
on the number of pieces, their time translate or the selected-plane offset. -/
theorem Family.exists_finite_cinematic_small_main_Lp_partition {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (ha : ∀ x ∈ tsupport χ, AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    (hdet : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (F : FrequencyCutoff) (βfreq : ℝ → ℝ) (hβfreq : ContDiff ℝ ∞ βfreq) :
    ∃ (I : Finset (tsupport χ)) (ψ : I → Cutoff d)
      (σ : I → (Fin 2 ↪ Fin (d + 2))) (ε : ℝ),
      0 < ε ∧ (∀ x, ∑ i : I, ψ i x = χ x) ∧
      ∀ i : I, ContDiff ℝ ∞ (ψ i) ∧ HasCompactSupport (ψ i) ∧
        tsupport (ψ i) ⊆ tsupport χ ∧
        ∀ p : ℝ, 2 < p → ∃ C : ℝ, 0 ≤ C ∧
          ∀ (b δ : ℝ) (N : ℕ) (u : UnselectedCoordinates (σ i))
            (f : Plane → ℂ), Integrable f → MemLp f (ENNReal.ofReal p) volume →
          ∀ κ r : ℝ, 0 < κ → 0 < r → 0 < δ → δ ≤ 1 → δ ≤ ε / 2 →
          (2 * Real.pi * r) * δ ^ (2 : ℕ) ∈ Icc (0 : ℝ) 1 →
          (∀ ξ : Plane, |ξ.2| < κ → F.bandSymbol 0 ξ * βfreq ξ.2 = 0) →
          eLpNorm (G.finiteSliceMain (ψ i) F βfreq r b δ N
            (fun z => parameterFrame d (((parameterFrame d).symm i.val.val.2 +
              selectedCoordinateSplit (σ i) (0, u)) + coordinateInsertion (σ i) z)) f)
            (ENNReal.ofReal p) (finiteSliceMainMeasure N) ≤
            ENNReal.ofReal ((C * κ⁻¹ * r⁻¹ * δ ^ (p - 2)) ^ (1 / p)) *
              eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨I, ψ, σ, ε, hε, hsum, hpatch⟩ :=
    G.exists_finite_cinematic_main_L2_partition χ hχ hc hχ0 ha hdet F βfreq
      hβfreq.continuous
  refine ⟨I, ψ, σ, ε, hε, hsum, ?_⟩
  intro i
  obtain ⟨hψ, hcψ, hsψ, β, C₂, M, hβ, hC₂, hM, _hsym, hL2⟩ := hpatch i
  have hapsi : ∀ x ∈ tsupport (ψ i),
      AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x :=
    fun x hx => ha x (hsψ hx)
  have hγpsi : ∀ x ∈ tsupport (ψ i), ContinuousAt (fun x => G.γ x.1 x.2) x :=
    fun x hx => (hapsi x hx).continuousAt
  obtain ⟨B, hB, hLinf⟩ := G.exists_uniform_finiteSliceMain_LInfinity (ψ i) hψ.continuous
    hcψ hγpsi F βfreq hβfreq
  refine ⟨hψ, hcψ, hsψ, ?_⟩
  intro p hp
  have hp0 : 0 < p := by linarith
  let C := 4 * p * ((3 * (C₂ ^ 2 * M ^ 2)) / β) * (2 * B) ^ (p - 2) / (p - 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro b δ N u f hf hfp κ r hκ hrpos hδ hδ1 hδε hα hgap
  let q : Aux 2 → Parameters 2 d := fun z =>
    parameterFrame d (((parameterFrame d).symm i.val.val.2 +
      selectedCoordinateSplit (σ i) (0, u)) + coordinateInsertion (σ i) z)
  have hq : Measurable q := by
    apply Continuous.measurable
    exact (parameterFrame d).continuous.comp
      (continuous_const.add (coordinateInsertion (σ i)).continuous)
  let T := G.finiteSliceMain (ψ i) F βfreq r b δ N q
  let A := (3 * (C₂ ^ 2 * M ^ 2 * κ⁻¹ * r⁻¹)) / β
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hadd : ∀ g h, Integrable g → Integrable h → ∀ w,
      T (fun x => g x + h x) w = T g w + T h w := by
    intro g h hg hh w
    exact congrFun (G.finiteSliceMain_add (ψ i) hψ.continuous hcψ hγpsi F βfreq
      hβfreq.continuous r b δ N q hg hh) w
  have hm : ∀ g, Integrable g → Measurable (T g) := by
    intro g hg
    exact G.measurable_finiteSliceMain (ψ i) hψ.continuous hcψ hapsi F βfreq
      hβfreq.continuous r b δ N q hq hg
  have h2 : ∀ g, Integrable g → Integrable (fun x => ‖g x‖ ^ 2) →
      (∫⁻ w, ENNReal.ofReal (‖T g w‖ ^ 2) ∂finiteSliceMainMeasure N) ≤
        ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) := by
    intro g hg hg2
    have hgp : MemLp g 2 volume := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mpr hg2
    have hh := hL2 b δ N u g hg hgp κ r hκ hrpos hδ hδ1 hδε hα hgap
    have hID : (∫⁻ w, ENNReal.ofReal (‖T g w‖ ^ 2) ∂finiteSliceMainMeasure N) =
        ∑ j ∈ Finset.range N, ∫⁻ z : Aux 2,
          ‖G.cutoffPartialExtension (scaleTimeLocalizedCutoff (ψ i) b δ j) F βfreq r g (q z)‖ₑ ^ (2 : ℕ) := by
      simp_rw [← enorm_sq_eq_ofReal_norm_sq]
      simpa only [ENNReal.rpow_two] using G.lintegral_finiteSliceMain (ψ i) hψ.continuous hcψ hapsi F βfreq
        hβfreq.continuous r b δ N q hq hg (2 : ℝ)
    change ENNReal.ofReal β * (∑ j ∈ Finset.range N, ∫⁻ z : Aux 2,
      ‖G.cutoffPartialExtension (scaleTimeLocalizedCutoff (ψ i) b δ j) F βfreq r g (q z)‖ₑ ^ (2 : ℕ)) ≤
      (3 : ℝ≥0∞) * ENNReal.ofReal (C₂ ^ 2 * M ^ 2 * κ⁻¹ * r⁻¹) *
        ∫⁻ x : Plane, ‖g x‖ₑ ^ (2 : ℕ) at hh
    rw [← hID] at hh
    simp only [enorm_sq_eq_ofReal_norm_sq] at hh
    have hcoef : (ENNReal.ofReal β)⁻¹ *
        ((3 : ℝ≥0∞) * ENNReal.ofReal (C₂ ^ 2 * M ^ 2 * κ⁻¹ * r⁻¹)) = ENNReal.ofReal A := by
      rw [← ENNReal.ofReal_inv_of_pos hβ]
      calc
        _ = ENNReal.ofReal β⁻¹ * ENNReal.ofReal (3 * (C₂ ^ 2 * M ^ 2 * κ⁻¹ * r⁻¹)) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
          norm_num
        _ = ENNReal.ofReal (β⁻¹ * (3 * (C₂ ^ 2 * M ^ 2 * κ⁻¹ * r⁻¹))) :=
          (ENNReal.ofReal_mul (inv_nonneg.mpr hβ.le)).symm
        _ = ENNReal.ofReal A := by congr 1; dsimp [A]; ring
    calc
      _ = (ENNReal.ofReal β)⁻¹ * (ENNReal.ofReal β *
          ∫⁻ w, ENNReal.ofReal (‖T g w‖ ^ 2) ∂finiteSliceMainMeasure N) :=
        (ENNReal.inv_mul_cancel_left (ENNReal.ofReal_pos.mpr hβ).ne' ENNReal.ofReal_ne_top).symm
      _ ≤ (ENNReal.ofReal β)⁻¹ *
          ((3 : ℝ≥0∞) * ENNReal.ofReal (C₂ ^ 2 * M ^ 2 * κ⁻¹ * r⁻¹) *
            ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2)) := mul_le_mul_right hh _
      _ = _ := by rw [← mul_assoc, hcoef]
  have hinf : ∀ g, Integrable g → ∀ M₀ : ℝ, 0 ≤ M₀ → (∀ x, ‖g x‖ ≤ M₀) →
      ∀ w, ‖T g w‖ ≤ (B * δ) * M₀ := by
    intro g hg M₀ hM₀ hgb w
    have hb := hLinf r hrpos b δ hδ N q g hg w
    have hginfty : eLpNorm g ∞ volume ≤ ENNReal.ofReal M₀ :=
      eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hgb)
    have ht : ‖T g w‖ₑ ≤ ENNReal.ofReal ((B * δ) * M₀) := by
      calc
        _ ≤ ENNReal.ofReal (B * δ) * eLpNorm g ∞ volume := hb
        _ ≤ ENNReal.ofReal (B * δ) * ENNReal.ofReal M₀ := mul_le_mul_right hginfty _
        _ = _ := (ENNReal.ofReal_mul (mul_nonneg hB.le hδ.le)).symm
    rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (by positivity)] at ht
    exact ht
  have hres := strong_L2_LInfinity_interpolation volume (finiteSliceMainMeasure N) T hadd hm
    hA (mul_pos hB hδ) h2 hinf hf hp hfp
  have hscale : 4 * p * A * (2 * (B * δ)) ^ (p - 2) / (p - 2) =
      C * κ⁻¹ * r⁻¹ * δ ^ (p - 2) := by
    rw [show 2 * (B * δ) = (2 * B) * δ by ring, Real.mul_rpow (by positivity) hδ.le]
    dsimp [A, C]
    ring
  rw [hscale] at hres
  exact hres

end PlanarNikodym
