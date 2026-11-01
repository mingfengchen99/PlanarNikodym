import PlanarNikodym.Analysis.Fourier.GlyzGeneralCurveTaylor
import PlanarNikodym.Analysis.Fourier.GlyzProjectedCurveNesting

/-! Every finest curve box lies in the Taylor-model box of its coarse
child, at the genuine Taylor scale threshold. Constants depend only on
derivative bounds, the actual jet determinant lower bound and box radius. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped BigOperators
namespace PlanarNikodym

theorem glyz_enlarged_taylor_box_affine_image {l : ℕ} (γ : ℝ → GlyzSpace l)
    (a s δ R : ℝ) (hδ : 0 < δ) (hR : 0 ≤ R)
    (L : GlyzSpace l ≃L[ℝ] GlyzSpace l)
    (hL : L.toContinuousLinearMap = glyzCurveJetOperator γ a) :
    glyzEnlargedCurveBox (glyzTaylorCurve γ l a) l s δ R =
      (fun ξ => γ a + glyzTaylorMomentLinear L ξ) ''
        glyzFrequencyBox (glyzMomentFrequencyFrame l (s - a) δ hδ)
          ((EuclideanSpace.equiv (Fin l) ℝ).symm (glyzMomentCurve l (s - a))) R := by
  rw [glyzFrequencyBox_eq_image, ← Set.image_comp]
  have hs : {v : Base l | ∀ j, |v j| ≤ R} = closedBall (0 : Base l) R := by
    ext v
    simp only [mem_setOf_eq, mem_closedBall, dist_zero_right,
      pi_norm_le_iff_of_nonneg hR, Real.norm_eq_abs]
  unfold glyzEnlargedCurveBox
  rw [hs]
  apply congrArg (fun F : Base l → GlyzSpace l => F '' closedBall 0 R)
  funext v
  simpa only [Function.comp_apply, glyzMomentFrequencyFrame_coordinates] using
    glyzCurveBoxPoint_taylor_affine_moment γ a s δ L hL v

theorem exists_uniform_glyz_moment_boxes_nearby (l : ℕ) {R : ℝ} (hR : 0 < R) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ (c s δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η),
      η ≤ δ → |s - c| ≤ δ →
      glyzFrequencyBox (glyzMomentFrequencyFrame l s η hη)
        ((EuclideanSpace.equiv (Fin l) ℝ).symm (glyzMomentCurve l s)) R ⊆
      glyzFrequencyBox (glyzMomentFrequencyFrame l c δ hδ)
        ((EuclideanSpace.equiv (Fin l) ℝ).symm (glyzMomentCurve l c)) Q := by
  obtain ⟨Q, hQ, hnest⟩ := exists_uniform_glyzMomentFrequencyBox_enlarged_nested l hR
  refine ⟨Q, hQ, fun c s δ η hδ hη hηδ hsc => ?_⟩
  have hrel : (s - c) / δ ∈ Icc (-1 : ℝ) 1 := by
    have h := abs_le.mp hsc
    constructor
    · exact (le_div_iff₀ hδ).mpr (by linarith)
    · exact (div_le_iff₀ hδ).mpr (by linarith)
  have h := hnest c δ ((s - c) / δ) (η / δ) hδ (div_pos hη hδ)
    hrel ((div_le_one hδ).mpr hηδ)
  have hcenter : c + δ * ((s - c) / δ) = s := by field_simp; ring
  have hscale : δ * (η / δ) = η := by field_simp
  simpa only [hcenter, hscale] using h

/-- Uniform support transfer directly from fine boxes of an arbitrary
controlled curve to the Taylor model at the child scale. -/
theorem exists_uniform_glyz_general_curve_taylor_nesting
    (l : ℕ) {β B R : ℝ} (hβ : 0 < β) (hB : 0 < B) (hR : 0 < R) :
    ∃ ρ Q : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 0 < Q ∧ ∀ γ : ℝ → GlyzSpace l,
      ContDiff ℝ (l + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ l + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, a < b → b - a < ρ →
      ∀ c ∈ Icc a b, ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ b - a →
      (b - a) ^ (l + 1) ≤ δ ^ l →
      ∃ T : GlyzSpace l ≃L[ℝ] GlyzSpace l,
        T.toContinuousLinearMap = glyzCurveJetOperator (glyzTaylorCurve γ l a) c ∧
        ∀ s ∈ Icc a b, ∀ (η : ℝ) (_hη : 0 < η), η ≤ δ → |s - c| ≤ δ →
          glyzEnlargedCurveBox γ l s η R ⊆
            glyzFrequencyBox (glyzScaledFrame T δ hδ) (glyzTaylorCurve γ l a c) Q := by
  obtain ⟨ρ, C, hρ, hρ1, hC, hframes⟩ := exists_uniform_glyz_general_taylor_inverse l hβ hB
  obtain ⟨_, _, hinverse⟩ := exists_uniform_glyz_general_curve_inverse l hβ hB
  obtain ⟨Q, hQ, hnest⟩ := exists_uniform_glyz_moment_boxes_nearby l hR
  let K : ℝ := (1 + (l : ℝ) * R) * B
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨ρ, Q + C * K, hρ, hρ1, by positivity, ?_⟩
  intro γ hγ hder hdet a ha b hb hab hshort c hc δ hδ hδκ hscale
  obtain ⟨T, hT, hTinv⟩ := hframes γ hγ hder hdet a ha b hb hab hshort c hc
  obtain ⟨L, hL, _⟩ := hinverse γ a (fun j => hder a ha _ (by omega)) (hdet a ha)
  refine ⟨T, hT, fun s hs η hη hηδ hsc ξ hξ => ?_⟩
  obtain ⟨v, hv, rfl⟩ := hξ
  let P := glyzTaylorCurve γ l a
  let ζ := glyzCurveBoxPoint P l s η v
  have hζ : ζ ∈ glyzFrequencyBox (glyzScaledFrame T δ hδ) (P c) Q := by
    rw [glyzTaylorFrequencyBox_affine_image γ a c δ Q hδ L T hL hT]
    have hξ : ζ ∈ glyzEnlargedCurveBox P l s η R := ⟨v, hv, rfl⟩
    rw [glyz_enlarged_taylor_box_affine_image γ a s η R hη hR.le L hL] at hξ
    apply (Set.image_mono (hnest (c - a) (s - a) δ η hδ hη hηδ ?_)) hξ
    simpa only [sub_sub_sub_cancel_right] using hsc
  have herr : ‖glyzCurveBoxPoint γ l s η v - ζ‖ ≤ K * δ ^ l :=
    (glyz_general_curve_box_taylor_bound l hB hR γ hγ
      (fun u hu => hder u hu _ le_rfl) ha hb hab hs hη (hηδ.trans hδκ) v hv).trans
      (mul_le_mul_of_nonneg_left hscale hK.le)
  apply glyz_scaled_box_add_ball_subset T hδ (hδκ.trans (hshort.le.trans hρ1)) hC.le hTinv (P c)
  exact ⟨ζ, hζ, glyzCurveBoxPoint γ l s η v - ζ,
    by simpa only [mem_closedBall, dist_zero_right] using herr, by abel_nf⟩

end PlanarNikodym
