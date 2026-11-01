import PlanarNikodym.Analysis.Fourier.GlyzProjectedInterpolation

/-! High-exponent interpolation for arbitrary affine frequency boxes.
The Fourier cutoffs and their uniform L¹ kernel bound are constructed
here. The only analytic hypothesis is the displayed critical estimate
on the explicitly enlarged boxes. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform ENNReal NNReal BigOperators
namespace PlanarNikodym

def glyzBoxCutoffRadius (m : ℕ) (R : ℝ) : ℝ :=
  (‖(EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap‖ + 1) * R

theorem glyzBoxCutoffRadius_pos (m : ℕ) {R : ℝ} (hR : 0 < R) :
    0 < glyzBoxCutoffRadius m R := by unfold glyzBoxCutoffRadius; positivity

theorem glyzBoxCutoff_eq_one {m : ℕ}
    (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) (a : GlyzSpace m)
    {R : ℝ} (hR : 0 < R) {ξ : GlyzSpace m}
    (hξ : ξ ∈ glyzFrequencyBox L a R) :
    glyzAffineCutoff L a (glyzBoxCutoffRadius m R) (glyzBoxCutoffRadius_pos m hR) ξ = 1 :=
  glyzBaseCutoff_eq_one _ _ (glyzFrequencyBox_subset_ball L a hR hξ)

/-- The uniform coefficient depends on the common box radius and
dimension, and precedes every frame, center, index family and input. -/
theorem exists_glyz_affine_boxes_supercritical (m : ℕ) {R : ℝ} (hR : 0 < R) :
    ∃ M : ℝ, 0 < M ∧ ∀ (ι : Type*) [Fintype ι] [Nonempty ι]
      (L : ι → GlyzSpace m ≃L[ℝ] GlyzSpace m) (a : ι → GlyzSpace m)
      (q : ℝ≥0), 2 ≤ q → ∀ (p D : ℝ), (q : ℝ) < p → 0 ≤ D →
      (∀ g : ι → SchwartzMap (GlyzSpace m) ℂ,
        (∀ i, Function.support (𝓕 (g i : GlyzSpace m → ℂ)) ⊆
          glyzFrequencyBox (L i) (a i) (glyzBoxCutoffRadius m R + 1)) →
        lpNorm ((∑ i, g i : SchwartzMap (GlyzSpace m) ℂ) : GlyzSpace m → ℂ)
            q volume ^ 2 ≤ D * ∑ i, lpNorm (g i : GlyzSpace m → ℂ) q volume ^ 2) →
      ∀ f : ι → SchwartzMap (GlyzSpace m) ℂ,
        (∀ i, Function.support (𝓕 (f i : GlyzSpace m → ℂ)) ⊆
          glyzFrequencyBox (L i) (a i) R) →
        (∫⁻ x, ENNReal.ofReal (‖(∑ i, f i : SchwartzMap (GlyzSpace m) ℂ) x‖ ^ p)) ≤
          ENNReal.ofReal (glyzInterpolationFactor p q * D ^ ((q : ℝ) / 2) *
            (Fintype.card ι : ℝ) ^ (p - (q : ℝ) / 2 - 1) * M ^ p) *
              ∑ i, ∫⁻ x, ENNReal.ofReal (‖f i x‖ ^ p) := by
  let K := glyzReproducingKernel
    (glyzBaseCutoff (E := GlyzSpace m) (glyzBoxCutoffRadius m R)
      (glyzBoxCutoffRadius_pos m hR))
  let M : ℝ := (∫ x, ‖K x‖) + 1
  have hM0 : 0 < M := by
    have hh : 0 ≤ ∫ x, ‖K x‖ := integral_nonneg fun x => norm_nonneg _
    dsimp only [M]
    linarith
  refine ⟨M, hM0, fun ι _ _ L a q hq p D hpq hD hcrit f hf => ?_⟩
  let χ := fun i => glyzAffineCutoff (L i) (a i) (glyzBoxCutoffRadius m R)
    (glyzBoxCutoffRadius_pos m hR)
  have hmass (i : ι) : (∫ x, ‖glyzReproducingKernel (χ i) x‖) ≤ M := by
    rw [integral_norm_glyzAffineKernel]
    change (∫ x, ‖K x‖) ≤ (∫ x, ‖K x‖) + 1
    linarith
  apply glyz_projected_supercritical_decoupling χ hq hpq hD hM0 hmass
  · intro g
    rw [glyzProjectionSum_apply]
    exact hcrit _ (fun i =>
      (support_fourier_glyzFourierProjector (χ i) (g i)).trans
        (support_glyzAffineCutoff_subset_box _ _ _ _))
  · exact fun i ξ hξ => glyzBoxCutoff_eq_one (L i) (a i) hR (hf i hξ)

end PlanarNikodym
