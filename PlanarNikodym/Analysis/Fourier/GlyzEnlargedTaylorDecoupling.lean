import PlanarNikodym.Analysis.Fourier.GlyzBandlimitedLocalization
import PlanarNikodym.Analysis.Fourier.GlyzTaylorDecoupling

/-! Taylor freezing for every fixed enlargement of the genuine projected
curve boxes, as required after Fourier localization and grouping. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped FourierTransform BigOperators ENNReal NNReal
namespace PlanarNikodym

def glyzEnlargedCurveBox {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (γ : ℝ → E) (l : ℕ) (s δ R : ℝ) : Set E :=
  glyzCurveBoxPoint γ l s δ '' {v : Base l | ∀ j, |v j| ≤ R}

theorem glyzCurveBoxPoint_eq_scaledFrame {l : ℕ}
    (γ : ℝ → GlyzSpace l) (s δ : ℝ) (hδ : 0 < δ)
    (L : GlyzSpace l ≃L[ℝ] GlyzSpace l)
    (hL : L.toContinuousLinearMap = glyzCurveJetOperator γ s) (v : Base l) :
    glyzCurveBoxPoint γ l s δ v = γ s +
      glyzScaledFrame L δ hδ ((EuclideanSpace.equiv (Fin l) ℝ).symm v) := by
  rw [glyzScaledFrame_apply]
  change _ = γ s + L.toContinuousLinearMap
    ((EuclideanSpace.equiv (Fin l) ℝ).symm (fun j => δ ^ ((j : ℕ) + 1) * v j))
  rw [hL, glyzCurveJetOperator_apply]
  rfl

theorem glyzEnlargedCurveBox_eq_frequencyBox {l : ℕ}
    (γ : ℝ → GlyzSpace l) (s δ R : ℝ) (hδ : 0 < δ) (hR : 0 ≤ R)
    (L : GlyzSpace l ≃L[ℝ] GlyzSpace l)
    (hL : L.toContinuousLinearMap = glyzCurveJetOperator γ s) :
    glyzEnlargedCurveBox γ l s δ R = glyzFrequencyBox (glyzScaledFrame L δ hδ) (γ s) R := by
  rw [glyzFrequencyBox_eq_image]
  have hs : {v : Base l | ∀ j, |v j| ≤ R} = closedBall (0 : Base l) R := by
    ext v
    simp only [mem_setOf_eq, mem_closedBall, dist_zero_right,
      pi_norm_le_iff_of_nonneg hR, Real.norm_eq_abs]
  unfold glyzEnlargedCurveBox
  rw [hs]
  apply congrArg (fun F : Base l → GlyzSpace l => F '' closedBall 0 R)
  funext v
  exact glyzCurveBoxPoint_eq_scaledFrame γ s δ hδ L hL v

/-- Scaling the Fourier-box coefficients preserves the affine center
exactly; this controls arbitrary fixed enlargements. -/
theorem glyzCurveBoxPoint_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (γ : ℝ → E) (l : ℕ) (s δ R : ℝ) (v : Base l) :
    glyzCurveBoxPoint γ l s δ (R • v) =
      (1 - R) • γ s + R • glyzCurveBoxPoint γ l s δ v := by
  simp only [glyzCurveBoxPoint, Pi.smul_apply, smul_eq_mul, smul_add, Finset.smul_sum, smul_smul]
  have hsum : (∑ j : Fin l, (δ ^ ((j : ℕ) + 1) * (R * v j)) • iteratedDeriv ((j : ℕ) + 1) γ s) =
      ∑ j : Fin l, (R * (δ ^ ((j : ℕ) + 1) * v j)) • iteratedDeriv ((j : ℕ) + 1) γ s := by
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    ring
  rw [hsum]
  module

/-- The uniform Taylor error remains of order kappa^(l+1) for all
coefficient boxes of a fixed positive radius. -/
theorem exists_uniform_glyzEnlargedCurveBoxPoint_taylor_bound (l r : ℕ) {R : ℝ} (hR : 0 < R) :
    ∃ K : ℝ, 0 < K ∧ ∀ t a b : ℝ,
      a ∈ Icc (-1 : ℝ) 1 → b ∈ Icc (-1 : ℝ) 1 → a < b →
      ∀ s ∈ Icc a b, ∀ δ : ℝ, 0 < δ → δ ≤ b - a →
      ∀ v : Base l, (∀ j, |v j| ≤ R) →
        ‖glyzCurveBoxPoint (glyzCoordinateCurve l r t) l s δ v -
          glyzCurveBoxPoint (glyzTaylorCurve (glyzCoordinateCurve l r t) l a) l s δ v‖ ≤
            K * (b - a) ^ (l + 1) := by
  obtain ⟨K, hK, hbound⟩ := exists_uniform_glyzCurveBoxPoint_taylor_bound l r
  refine ⟨(R + |1 - R|) * K, mul_pos (by positivity) hK, ?_⟩
  intro t a b ha hb hab s hs δ hδ hδκ v hv
  let w : Base l := R⁻¹ • v
  have hw : ∀ j, |w j| ≤ 1 := by
    intro j
    change |R⁻¹ * v j| ≤ 1
    rw [abs_mul, abs_inv, abs_of_pos hR]
    calc
      _ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left (hv j) (by positivity)
      _ = 1 := inv_mul_cancel₀ hR.ne'
  have hunit := hbound t a b ha hb hab s hs δ hδ hδκ w hw
  have hzero := hbound t a b ha hb hab s hs δ hδ hδκ 0 (by intro j; simp)
  have hvw : R • w = v := by simp [w, smul_smul, hR.ne']
  have he : glyzCurveBoxPoint (glyzCoordinateCurve l r t) l s δ v -
      glyzCurveBoxPoint (glyzTaylorCurve (glyzCoordinateCurve l r t) l a) l s δ v =
      R • (glyzCurveBoxPoint (glyzCoordinateCurve l r t) l s δ w -
        glyzCurveBoxPoint (glyzTaylorCurve (glyzCoordinateCurve l r t) l a) l s δ w) +
      (1 - R) • (glyzCurveBoxPoint (glyzCoordinateCurve l r t) l s δ 0 -
        glyzCurveBoxPoint (glyzTaylorCurve (glyzCoordinateCurve l r t) l a) l s δ 0) := by
    have h₁ := glyzCurveBoxPoint_smul (glyzCoordinateCurve l r t) l s δ R w
    have h₂ := glyzCurveBoxPoint_smul (glyzTaylorCurve (glyzCoordinateCurve l r t) l a) l s δ R w
    rw [hvw] at h₁ h₂
    rw [h₁, h₂]
    simp only [glyzCurveBoxPoint, Pi.zero_apply, mul_zero, zero_smul, Finset.sum_const_zero, add_zero]
    simp only [smul_add, smul_sub]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hR]
  calc
    _ ≤ R * (K * (b - a) ^ (l + 1)) + |1 - R| * (K * (b - a) ^ (l + 1)) :=
      add_le_add (mul_le_mul_of_nonneg_left hunit hR.le)
        (mul_le_mul_of_nonneg_left hzero (abs_nonneg _))
    _ = _ := by ring

/-- Every fixed enlargement of the actual curve boxes is contained in
an explicitly enlarged Taylor box, uniformly in all separated centers. -/
theorem exists_uniform_glyzEnlargedCurveBox_taylor_inclusion
    (l r : ℕ) {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) :
    ∃ ρ Q : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 0 < Q ∧ ∀ t a b : ℝ,
      a ∈ Icc (-1 : ℝ) 1 → b ∈ Icc (-1 : ℝ) 1 → a < b → b - a < ρ →
      ∀ s ∈ Icc a b, (s, t) ∈ separatedMixedCenters ν →
      ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ b - a → (b - a) ^ (l + 1) ≤ δ ^ l →
        ∃ T : GlyzSpace l ≃L[ℝ] GlyzSpace l,
          T.toContinuousLinearMap =
            glyzCurveJetOperator (glyzTaylorCurve (glyzCoordinateCurve l r t) l a) s ∧
          glyzEnlargedCurveBox (glyzCoordinateCurve l r t) l s δ R ⊆
            glyzFrequencyBox (glyzScaledFrame T δ hδ)
              (glyzTaylorCurve (glyzCoordinateCurve l r t) l a s) Q := by
  obtain ⟨ρ, C, hρ, hρ1, hC, hstable⟩ := exists_uniform_glyzTaylorCurve_inverse l r hν
  obtain ⟨K, hK, herror⟩ := exists_uniform_glyzEnlargedCurveBoxPoint_taylor_bound l r hR
  refine ⟨ρ, R + C * K, hρ, hρ1, by positivity, ?_⟩
  intro t a b ha hb hab hshort s hs hsep δ hδ hδκ hscale
  obtain ⟨T, hT, hinv⟩ := hstable t a b ha hb hab hshort s hs hsep
  refine ⟨T, hT, ?_⟩
  rintro ξ ⟨v, hv, rfl⟩
  let P := glyzTaylorCurve (glyzCoordinateCurve l r t) l a
  let η := glyzCurveBoxPoint P l s δ v
  have hη : η ∈ glyzFrequencyBox (glyzScaledFrame T δ hδ) (P s) R := by
    rw [← glyzEnlargedCurveBox_eq_frequencyBox P s δ R hδ hR.le T hT]
    exact ⟨v, hv, rfl⟩
  have herr : ‖glyzCurveBoxPoint (glyzCoordinateCurve l r t) l s δ v - η‖ ≤ K * δ ^ l :=
    (herror t a b ha hb hab s hs δ hδ hδκ v hv).trans
      (mul_le_mul_of_nonneg_left hscale hK.le)
  apply glyz_scaled_box_add_ball_subset T hδ (hδκ.trans ((hshort.trans_le hρ1).le)) hC.le hinv (P s)
  exact ⟨η, hη, glyzCurveBoxPoint (glyzCoordinateCurve l r t) l s δ v - η,
    by simpa only [mem_closedBall, dist_zero_right] using herr, by abel_nf⟩

/-- The genuine one-step norm inequality allows every fixed enlargement
of the controlled curve boxes. Its enlarged moment-box induction input
is stated explicitly, with the enlargement Q constructed from R. -/
theorem exists_uniform_glyzCoordinateCurve_enlarged_decoupling_step
    (l r : ℕ) {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) :
    ∃ ρ Q : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 0 < Q ∧
      ∀ (t a b : ℝ), a ∈ Icc (-1 : ℝ) 1 → b ∈ Icc (-1 : ℝ) 1 →
      a < b → b - a < ρ → (a, t) ∈ separatedMixedCenters ν →
      ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ b - a → (b - a) ^ (l + 1) ≤ δ ^ l →
      ∀ (I : Finset ℕ) (s : ℕ → ℝ) (f : ℕ → SchwartzMap (GlyzSpace l) ℂ)
      (p : ℝ≥0∞) (D : ℝ),
      (∀ i ∈ I, s i ∈ Icc a b ∧ (s i, t) ∈ separatedMixedCenters ν) →
      (∀ i ∈ I, Function.support (𝓕 (f i : GlyzSpace l → ℂ)) ⊆
        glyzEnlargedCurveBox (glyzCoordinateCurve l r t) l (s i) δ R) →
      (∀ g : ℕ → SchwartzMap (GlyzSpace l) ℂ,
        (∀ i ∈ I, Function.support (𝓕 (g i : GlyzSpace l → ℂ)) ⊆
          glyzFrequencyBox (glyzMomentFrequencyFrame l (s i - a) δ hδ)
            ((EuclideanSpace.equiv (Fin l) ℝ).symm (glyzMomentCurve l (s i - a))) Q) →
        lpNorm ((∑ i ∈ I, g i : SchwartzMap (GlyzSpace l) ℂ) : GlyzSpace l → ℂ) p volume ^ 2 ≤
          D * ∑ i ∈ I, lpNorm (g i : GlyzSpace l → ℂ) p volume ^ 2) →
      lpNorm ((∑ i ∈ I, f i : SchwartzMap (GlyzSpace l) ℂ) : GlyzSpace l → ℂ) p volume ^ 2 ≤
        D * ∑ i ∈ I, lpNorm (f i : GlyzSpace l → ℂ) p volume ^ 2 := by
  obtain ⟨ρ, Q, hρ, hρ1, hQ, hincl⟩ :=
    exists_uniform_glyzEnlargedCurveBox_taylor_inclusion l r hν hR
  obtain ⟨_, _, hframe⟩ := exists_uniform_glyzCoordinateCurve_inverse l r hν
  refine ⟨ρ, Q, hρ, hρ1, hQ, fun t a b ha hb hab hshort hsep δ hδ hδκ hscale
    I s f p D hs hf hD => ?_⟩
  obtain ⟨L, hL, _⟩ := hframe (a, t) hsep
  apply glyz_taylor_decoupling_transfer (glyzCoordinateCurve l r t) a δ Q hδ L hL I s f p D ?_ hD
  intro i hi
  obtain ⟨T, hT, hincl⟩ := hincl t a b ha hb hab hshort (s i) (hs i hi).1 (hs i hi).2
    δ hδ hδκ hscale
  exact ⟨T, hT, (hf i hi).trans hincl⟩

end PlanarNikodym
