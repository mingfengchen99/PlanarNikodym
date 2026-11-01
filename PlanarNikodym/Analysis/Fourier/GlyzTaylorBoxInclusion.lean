import PlanarNikodym.Analysis.Fourier.GlyzTaylorFrameStability
import PlanarNikodym.Analysis.Fourier.GlyzScaledCurveFrame

/-! Actual Taylor-box inclusion at the induction-on-scales threshold
kappa^(l+1) <= delta^l. The enlargement and the short-interval threshold
are uniform in all separated projection centers. -/
noncomputable section
open Set
namespace PlanarNikodym

theorem exists_uniform_glyzCurveBox_taylor_inclusion (l r : ℕ) {ν : ℝ} (hν : 0 < ν) :
    ∃ ρ R : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 0 < R ∧ ∀ t a b : ℝ,
      a ∈ Icc (-1 : ℝ) 1 → b ∈ Icc (-1 : ℝ) 1 → a < b → b - a < ρ →
      ∀ s ∈ Icc a b, (s, t) ∈ separatedMixedCenters ν →
      ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ b - a → (b - a) ^ (l + 1) ≤ δ ^ l →
        ∃ T : GlyzSpace l ≃L[ℝ] GlyzSpace l,
          T.toContinuousLinearMap =
            glyzCurveJetOperator (glyzTaylorCurve (glyzCoordinateCurve l r t) l a) s ∧
          glyzCurveBox (glyzCoordinateCurve l r t) l s δ ⊆
            glyzFrequencyBox (glyzScaledFrame T δ hδ)
              (glyzTaylorCurve (glyzCoordinateCurve l r t) l a s) R := by
  obtain ⟨ρ, C, hρ, hρ1, hC, hstable⟩ := exists_uniform_glyzTaylorCurve_inverse l r hν
  obtain ⟨K, hK, herror⟩ := exists_uniform_glyzCurveBoxPoint_taylor_bound l r
  refine ⟨ρ, 1 + C * K, hρ, hρ1, by positivity, ?_⟩
  intro t a b ha hb hab hshort s hs hsep δ hδ hδκ hscale
  obtain ⟨T, hT, hinv⟩ := hstable t a b ha hb hab hshort s hs hsep
  refine ⟨T, hT, ?_⟩
  rintro ξ ⟨v, hv, rfl⟩
  let P := glyzTaylorCurve (glyzCoordinateCurve l r t) l a
  have hη : glyzCurveBoxPoint P l s δ v ∈
      glyzFrequencyBox (glyzScaledFrame T δ hδ) (P s) 1 := by
    rw [← glyzCurveBox_eq_frequencyBox P s δ hδ T hT]
    exact ⟨v, hv, rfl⟩
  apply glyzFrequencyBox_absorb_error T hδ (hδκ.trans ((hshort.trans_le hρ1).le))
    hC.le hinv (P s) _ _ hη
  exact (herror t a b ha hb hab s hs δ hδ hδκ v hv).trans
    (mul_le_mul_of_nonneg_left hscale hK.le)

end PlanarNikodym
