import PlanarNikodym.Analysis.Fourier.GlyzTaylorBoxInclusion
import PlanarNikodym.Analysis.Fourier.GlyzTaylorFrequencyImage
import PlanarNikodym.Analysis.Fourier.GlyzAffineLpTransfer

/-! The analytic Taylor-freezing step for the actual projected curve.
The input estimate is for enlarged moment boxes. The passage from the
unit-box moment theorem to that enlarged-box estimate is not assumed
implicitly and remains a separate frequency-subdivision task. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped FourierTransform ENNReal NNReal BigOperators
namespace PlanarNikodym

/-- Exact affine identification of every enlarged Taylor box, not only
the radius-one boxes. -/
theorem glyzTaylorFrequencyBox_affine_image {l : ℕ}
    (γ : ℝ → GlyzSpace l) (a s δ R : ℝ) (hδ : 0 < δ)
    (L T : GlyzSpace l ≃L[ℝ] GlyzSpace l)
    (hL : L.toContinuousLinearMap = glyzCurveJetOperator γ a)
    (hT : T.toContinuousLinearMap = glyzCurveJetOperator (glyzTaylorCurve γ l a) s) :
    glyzFrequencyBox (glyzScaledFrame T δ hδ) (glyzTaylorCurve γ l a s) R =
      (fun ξ => γ a + glyzTaylorMomentLinear L ξ) ''
        glyzFrequencyBox (glyzMomentFrequencyFrame l (s - a) δ hδ)
          ((EuclideanSpace.equiv (Fin l) ℝ).symm (glyzMomentCurve l (s - a))) R := by
  rw [glyzFrequencyBox_eq_image, glyzFrequencyBox_eq_image, ← Set.image_comp]
  apply congrArg (fun F : Base l → GlyzSpace l => F '' closedBall 0 R)
  funext v
  have he : glyzTaylorCurve γ l a s +
      glyzScaledFrame T δ hδ ((EuclideanSpace.equiv (Fin l) ℝ).symm v) =
        glyzCurveBoxPoint (glyzTaylorCurve γ l a) l s δ v := by
    rw [glyzScaledFrame_apply]
    change _ + T.toContinuousLinearMap
      ((EuclideanSpace.equiv (Fin l) ℝ).symm
        (fun j => δ ^ ((j : ℕ) + 1) * v j)) = _
    rw [hT, glyzCurveJetOperator_apply]
    rfl
  change _ = γ a + glyzTaylorMomentLinear L (_ + _)
  rw [he, glyzCurveBoxPoint_taylor_affine_moment γ a s δ L hL v,
    glyzMomentFrequencyFrame_coordinates]

/-- Construct the actual pullback of a Taylor-supported piece and
identify its enlarged moment Fourier support. -/
theorem support_fourier_glyzTaylor_pullback {l : ℕ}
    (γ : ℝ → GlyzSpace l) (a s δ R : ℝ) (hδ : 0 < δ)
    (L T : GlyzSpace l ≃L[ℝ] GlyzSpace l)
    (hL : L.toContinuousLinearMap = glyzCurveJetOperator γ a)
    (hT : T.toContinuousLinearMap = glyzCurveJetOperator (glyzTaylorCurve γ l a) s)
    (f : SchwartzMap (GlyzSpace l) ℂ)
    (hf : Function.support (𝓕 (f : GlyzSpace l → ℂ)) ⊆
      glyzFrequencyBox (glyzScaledFrame T δ hδ) (glyzTaylorCurve γ l a s) R) :
    Function.support (𝓕 (glyzSchwartzFrequencyAffine (glyzTaylorMomentLinear L).symm
      (-((glyzTaylorMomentLinear L).symm (γ a))) f : GlyzSpace l → ℂ)) ⊆
      glyzFrequencyBox (glyzMomentFrequencyFrame l (s - a) δ hδ)
        ((EuclideanSpace.equiv (Fin l) ℝ).symm (glyzMomentCurve l (s - a))) R := by
  intro ξ hξ
  rw [support_fourier_glyzSchwartzFrequencyAffine] at hξ
  obtain ⟨η, hη, rfl⟩ := hξ
  have hm := hf hη
  rw [glyzTaylorFrequencyBox_affine_image γ a s δ R hδ L T hL hT] at hm
  obtain ⟨ζ, hζ, rfl⟩ := hm
  simpa only [map_add, ContinuousLinearEquiv.symm_apply_apply, neg_add_cancel_left] using hζ

/-- The actual norm inequality for finitely many Taylor-supported
pieces. Its sole analytic premise is the enlarged moment-box estimate. -/
theorem glyz_taylor_decoupling_transfer {l : ℕ}
    (γ : ℝ → GlyzSpace l) (a δ R : ℝ) (hδ : 0 < δ)
    (L : GlyzSpace l ≃L[ℝ] GlyzSpace l)
    (hL : L.toContinuousLinearMap = glyzCurveJetOperator γ a)
    (I : Finset ℕ) (s : ℕ → ℝ) (f : ℕ → SchwartzMap (GlyzSpace l) ℂ)
    (p : ℝ≥0∞) (D : ℝ)
    (hf : ∀ i ∈ I, ∃ T : GlyzSpace l ≃L[ℝ] GlyzSpace l,
      T.toContinuousLinearMap = glyzCurveJetOperator (glyzTaylorCurve γ l a) (s i) ∧
      Function.support (𝓕 (f i : GlyzSpace l → ℂ)) ⊆
        glyzFrequencyBox (glyzScaledFrame T δ hδ) (glyzTaylorCurve γ l a (s i)) R)
    (hD : ∀ g : ℕ → SchwartzMap (GlyzSpace l) ℂ,
      (∀ i ∈ I, Function.support (𝓕 (g i : GlyzSpace l → ℂ)) ⊆
        glyzFrequencyBox (glyzMomentFrequencyFrame l (s i - a) δ hδ)
          ((EuclideanSpace.equiv (Fin l) ℝ).symm (glyzMomentCurve l (s i - a))) R) →
      lpNorm ((∑ i ∈ I, g i : SchwartzMap (GlyzSpace l) ℂ) : GlyzSpace l → ℂ) p volume ^ 2 ≤
        D * ∑ i ∈ I, lpNorm (g i : GlyzSpace l → ℂ) p volume ^ 2) :
    lpNorm ((∑ i ∈ I, f i : SchwartzMap (GlyzSpace l) ℂ) : GlyzSpace l → ℂ) p volume ^ 2 ≤
      D * ∑ i ∈ I, lpNorm (f i : GlyzSpace l → ℂ) p volume ^ 2 := by
  apply glyz_affine_decoupling_transfer (glyzTaylorMomentLinear L).symm
    (-((glyzTaylorMomentLinear L).symm (γ a))) I f p D
  apply hD
  intro i hi
  obtain ⟨T, hT, hsupp⟩ := hf i hi
  exact support_fourier_glyzTaylor_pullback γ a (s i) δ R hδ L T hL hT (f i) hsupp

/-- Actual one-step decoupling of the projected curve at the Taylor
scale threshold. The uniform constants are constructed before centers,
scales, finite families and functions. Enlarged moment boxes are explicit. -/
theorem exists_uniform_glyzCoordinateCurve_decoupling_step
    (l r : ℕ) {ν : ℝ} (hν : 0 < ν) :
    ∃ ρ R : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 0 < R ∧
      ∀ (t a b : ℝ), a ∈ Icc (-1 : ℝ) 1 → b ∈ Icc (-1 : ℝ) 1 →
      a < b → b - a < ρ → (a, t) ∈ separatedMixedCenters ν →
      ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ b - a → (b - a) ^ (l + 1) ≤ δ ^ l →
      ∀ (I : Finset ℕ) (s : ℕ → ℝ) (f : ℕ → SchwartzMap (GlyzSpace l) ℂ)
      (p : ℝ≥0∞) (D : ℝ),
      (∀ i ∈ I, s i ∈ Icc a b ∧ (s i, t) ∈ separatedMixedCenters ν) →
      (∀ i ∈ I, Function.support (𝓕 (f i : GlyzSpace l → ℂ)) ⊆
        glyzCurveBox (glyzCoordinateCurve l r t) l (s i) δ) →
      (∀ g : ℕ → SchwartzMap (GlyzSpace l) ℂ,
        (∀ i ∈ I, Function.support (𝓕 (g i : GlyzSpace l → ℂ)) ⊆
          glyzFrequencyBox (glyzMomentFrequencyFrame l (s i - a) δ hδ)
            ((EuclideanSpace.equiv (Fin l) ℝ).symm (glyzMomentCurve l (s i - a))) R) →
        lpNorm ((∑ i ∈ I, g i : SchwartzMap (GlyzSpace l) ℂ) : GlyzSpace l → ℂ) p volume ^ 2 ≤
          D * ∑ i ∈ I, lpNorm (g i : GlyzSpace l → ℂ) p volume ^ 2) →
      lpNorm ((∑ i ∈ I, f i : SchwartzMap (GlyzSpace l) ℂ) : GlyzSpace l → ℂ) p volume ^ 2 ≤
        D * ∑ i ∈ I, lpNorm (f i : GlyzSpace l → ℂ) p volume ^ 2 := by
  obtain ⟨ρ, R, hρ, hρ1, hR, hincl⟩ := exists_uniform_glyzCurveBox_taylor_inclusion l r hν
  obtain ⟨_, _, hframe⟩ := exists_uniform_glyzCoordinateCurve_inverse l r hν
  refine ⟨ρ, R, hρ, hρ1, hR, fun t a b ha hb hab hshort hsep δ hδ hδκ hscale
    I s f p D hs hf hD => ?_⟩
  obtain ⟨L, hL, _⟩ := hframe (a, t) hsep
  apply glyz_taylor_decoupling_transfer (glyzCoordinateCurve l r t) a δ R hδ L hL I s f p D ?_ hD
  intro i hi
  obtain ⟨T, hT, hincl⟩ := hincl t a b ha hb hab hshort (s i) (hs i hi).1 (hs i hi).2
    δ hδ hδκ hscale
  exact ⟨T, hT, (hf i hi).trans hincl⟩

/-- Convert the actual squared-norm decoupling estimate to the power
integrals consumed by the local weighted and bilinear assembly. -/
theorem glyz_square_decoupling_to_power_integrals {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (I : Finset ℕ) (f : ℕ → SchwartzMap E ℂ) {p : ℝ≥0} (hp : 0 < p)
    {D : ℝ} (hD : 0 ≤ D)
    (h : lpNorm ((∑ i ∈ I, f i : SchwartzMap E ℂ) : E → ℂ) p volume ^ 2 ≤
      D * ∑ i ∈ I, lpNorm (f i : E → ℂ) p volume ^ 2) :
    (∫⁻ x, ‖(∑ i ∈ I, f i) x‖ₑ ^ (p : ℝ)) ≤ ENNReal.ofReal D ^ ((p : ℝ) / 2) *
      (∑ i ∈ I, (∫⁻ x, ‖f i x‖ₑ ^ (p : ℝ)) ^ (2 / (p : ℝ))) ^ ((p : ℝ) / 2) := by
  have hp' : (0 : ℝ) < p := hp
  have hsq : eLpNorm ((∑ i ∈ I, f i : SchwartzMap E ℂ) : E → ℂ) p volume ^ (2 : ℕ) ≤
      ENNReal.ofReal (D * ∑ i ∈ I, lpNorm (f i : E → ℂ) p volume ^ 2) := by
    rw [← ofReal_lpNorm ((∑ i ∈ I, f i : SchwartzMap E ℂ).memLp p volume),
      ← ENNReal.ofReal_pow lpNorm_nonneg]
    exact ENNReal.ofReal_le_ofReal h
  have hpower := ENNReal.rpow_le_rpow hsq (show 0 ≤ (p : ℝ) / 2 by positivity)
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, Nat.cast_ofNat,
    show (2 : ℝ) * ((p : ℝ) / 2) = p by ring,
    eLpNorm_nnreal_pow_eq_lintegral hp.ne', ENNReal.ofReal_mul hD,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)] at hpower
  have hi (i : ℕ) : ENNReal.ofReal (lpNorm (f i : E → ℂ) p volume ^ (2 : ℕ)) =
      (∫⁻ x, ‖f i x‖ₑ ^ (p : ℝ)) ^ (2 / (p : ℝ)) := by
    rw [← eLpNorm_nnreal_pow_eq_lintegral hp.ne', ← ENNReal.rpow_mul,
      show (p : ℝ) * (2 / (p : ℝ)) = 2 by field_simp,
      ENNReal.rpow_two, ← ofReal_lpNorm ((f i).memLp p volume),
      ENNReal.ofReal_pow lpNorm_nonneg]
  simpa only [hi] using hpower

end PlanarNikodym
