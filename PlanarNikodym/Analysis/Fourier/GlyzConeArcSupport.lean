import PlanarNikodym.Analysis.Fourier.GlyzCurveArcSupport
import PlanarNikodym.Analysis.Fourier.GlyzConeThickening

/-! Actual parametrized cone patches and their Euclidean neighborhoods
have the derivative-box supports required by the proved cone estimates. -/
noncomputable section
open Set Metric MeasureTheory
open scoped Pointwise
namespace PlanarNikodym

def glyzConeArc (k : ℕ) (γ : ℝ → GlyzSpace k) (I : Set ℝ) (rmin rmax : ℝ) :
    Set (GlyzConeSpace k) :=
  (fun z : ℝ × ℝ => WithLp.toLp 2 (z.2 • γ z.1, z.2)) '' (I ×ˢ Icc rmin rmax)

theorem isCompact_glyzConeArc (k : ℕ) (γ : ℝ → GlyzSpace k) (hγ : Continuous γ)
    (I : Set ℝ) (hI : IsCompact I) (rmin rmax : ℝ) :
    IsCompact (glyzConeArc k γ I rmin rmax) := by
  apply (hI.prod isCompact_Icc).image
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ (GlyzSpace k) ℝ).symm.continuous.comp
    ((continuous_snd.smul (hγ.comp continuous_fst)).prodMk continuous_snd)

theorem exists_uniform_glyz_cone_arc_neighborhood_support (k : ℕ) {β B S rmin : ℝ}
    (hβ : 0 < β) (hB : 0 < B) (hS : 0 < S) (hrmin : 0 < rmin) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ γ : ℝ → GlyzSpace k,
      ContDiff ℝ (k + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ k + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ c ∈ Icc (0 : ℝ) 1, ∀ (δ rmax : ℝ),
      0 < δ → δ ≤ 1 → S * δ ^ k ≤ rmin / 2 →
      ∀ I : Set ℝ, I ⊆ Icc (0 : ℝ) 1 → (∀ t ∈ I, |t - c| ≤ δ) →
      glyzConeArc k γ I rmin rmax + closedBall (0 : GlyzConeSpace k) (S * δ ^ k) ⊆
        glyzConeBox k γ c δ Q (rmin / 2) (rmax + rmin / 2) := by
  obtain ⟨R, hR, harc⟩ := exists_uniform_glyz_curve_arc_support k hβ hB
  obtain ⟨Q, hQ, hthick⟩ := exists_uniform_glyz_cone_thickening k hβ hB hR hS hrmin
  refine ⟨Q, hQ, fun γ hγ hder hdet c hc δ rmax hδ hδ1 hsmall I hI htc => ?_⟩
  have hs : glyzConeArc k γ I rmin rmax ⊆ glyzConeBox k γ c δ R rmin rmax := by
    rintro z ⟨⟨t, r⟩, ⟨ht, hr⟩, rfl⟩
    exact ⟨r, hr, γ t, harc γ hγ hder hdet c hc t (hI ht) δ hδ hδ1 (htc t ht), rfl⟩
  exact (add_subset_add hs (Subset.refl _)).trans (hthick γ c δ rmax hδ hδ1 hsmall
    (fun j hj => hder c hc j (by omega)) (hdet c hc))

end PlanarNikodym
