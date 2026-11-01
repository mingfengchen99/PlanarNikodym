import PlanarNikodym.Analysis.Fourier.FourierIntegralL2
import Mathlib.Algebra.Order.Chebyshev

/-! L² decoupling from actual Fourier overlap. This supplies the analytic
base mechanism for the GLYZ dimension induction. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform Classical ENNReal
namespace PlanarNikodym

theorem norm_sum_sq_le_overlap {ι : Type*} (I : Finset ι) (v : ι → ℂ)
    (B : ℕ) (hB : (I.filter (fun i => v i ≠ 0)).card ≤ B) :
    ‖∑ i ∈ I, v i‖ ^ (2 : ℕ) ≤ (B : ℝ) * ∑ i ∈ I, ‖v i‖ ^ (2 : ℕ) := by
  let J := I.filter (fun i => v i ≠ 0)
  have he : ∑ i ∈ I, v i = ∑ i ∈ J, v i := by
    symm
    exact Finset.sum_filter_of_ne (fun i _ hi => hi)
  have he' : ∑ i ∈ J, ‖v i‖ ^ (2 : ℕ) = ∑ i ∈ I, ‖v i‖ ^ (2 : ℕ) := by
    apply Finset.sum_filter_of_ne
    intro i _ hi
    simpa using hi
  calc
    _ ≤ (∑ i ∈ J, ‖v i‖) ^ (2 : ℕ) := by
      rw [he]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _
    _ ≤ (J.card : ℝ) * ∑ i ∈ J, ‖v i‖ ^ (2 : ℕ) := sq_sum_le_card_mul_sum_sq
    _ ≤ _ := by
      rw [he']
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hB) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem enorm_sum_sq_le_overlap {ι : Type*} (I : Finset ι) (v : ι → ℂ)
    (B : ℕ) (hB : (I.filter (fun i => v i ≠ 0)).card ≤ B) :
    ‖∑ i ∈ I, v i‖ₑ ^ (2 : ℕ) ≤ (B : ℝ≥0∞) * ∑ i ∈ I, ‖v i‖ₑ ^ (2 : ℕ) := by
  have h := ENNReal.ofReal_le_ofReal (norm_sum_sq_le_overlap I v B hB)
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg B), ENNReal.ofReal_natCast,
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using h

theorem glyz_schwartz_l2_overlap {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (I : Finset ι) (f : ι → SchwartzMap E ℂ) (B : ℕ)
    (hB : ∀ ξ, (I.filter (fun i => 𝓕 (f i : E → ℂ) ξ ≠ 0)).card ≤ B) :
    (∫⁻ x : E, ‖∑ i ∈ I, f i x‖ₑ ^ (2 : ℕ)) ≤
      (B : ℝ≥0∞) * ∑ i ∈ I, ∫⁻ x : E, ‖f i x‖ₑ ^ (2 : ℕ) := by
  let F : SchwartzMap E ℂ := ∑ i ∈ I, f i
  have he : (fun ξ : E => ∑ i ∈ I, 𝓕 (f i : E → ℂ) ξ) = 𝓕 (F : E → ℂ) := by
    funext ξ
    change (∑ i ∈ I, 𝓕 (f i) ξ) = 𝓕 F ξ
    simp [F]
  have hF : (fun x : E => ∑ i ∈ I, f i x) = F := by ext x; simp [F]
  calc
    _ = ∫⁻ ξ : E, ‖∑ i ∈ I, 𝓕 (f i : E → ℂ) ξ‖ₑ ^ (2 : ℕ) := by
      have hp := (lintegral_fourierIntegral_sq F.integrable (F.memLp 2)).symm
      exact ((congrArg (fun g : E → ℂ => ∫⁻ x, ‖g x‖ₑ ^ (2 : ℕ)) hF).trans hp).trans
        (congrArg (fun g : E → ℂ => ∫⁻ x, ‖g x‖ₑ ^ (2 : ℕ)) he.symm)
    _ ≤ ∫⁻ ξ : E, (B : ℝ≥0∞) * ∑ i ∈ I, ‖𝓕 (f i : E → ℂ) ξ‖ₑ ^ (2 : ℕ) :=
      lintegral_mono (fun ξ => enorm_sum_sq_le_overlap I _ B (hB ξ))
    _ = _ := by
      rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top B), lintegral_finsetSum]
      · congr 1
        apply Finset.sum_congr rfl
        intro i _
        exact lintegral_fourierIntegral_sq (f i).integrable ((f i).memLp 2)
      · intro i _
        exact ((𝓕 (f i)).continuous.measurable.enorm.pow_const _)

end PlanarNikodym
