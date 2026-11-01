import PlanarNikodym.Analysis.Fourier.GlyzCylindricalDecoupling
import PlanarNikodym.Analysis.Fourier.GlyzEnlargedMomentDecoupling
import PlanarNikodym.Analysis.Fourier.GlyzCriticalMomentDecoupling

/-! Critical moment decoupling in a larger ambient space, with unrestricted
extra Fourier coordinates. The estimate follows from actual spatial
slices; its coefficient is independent of the extra coordinate. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform ENNReal NNReal BigOperators
namespace PlanarNikodym

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem glyz_cylindrical_moment_decoupling_of_admissible_loss
    {k : ℕ} {p : ℝ≥0} (hp : 2 ≤ p) {ε : ℝ}
    (hε : GlyzAdmissibleSquareLoss k p ε) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ∀ f : ℕ → SchwartzMap (WithLp 2 (GlyzSpace k × V)) ℂ,
      (∀ i ∈ Finset.range (2 ^ N),
        Function.support (𝓕 (f i : WithLp 2 (GlyzSpace k × V) → ℂ)) ⊆
          {z | (WithLp.ofLp z).1 ∈
            glyzFrequencyBox (glyzMomentFrequencyFrame k (glyzDyadicCenter N i)
              (glyzDyadicScale N) (glyzDyadicScale_pos N))
              ((EuclideanSpace.equiv (Fin k) ℝ).symm
                (glyzMomentCurve k (glyzDyadicCenter N i))) R}) →
      lpNorm ((∑ i ∈ Finset.range (2 ^ N), f i :
        SchwartzMap (WithLp 2 (GlyzSpace k × V)) ℂ) :
          WithLp 2 (GlyzSpace k × V) → ℂ) p volume ^ 2 ≤
        C * (2 : ℝ) ^ (ε * N) *
          ∑ i ∈ Finset.range (2 ^ N), lpNorm (f i :
            WithLp 2 (GlyzSpace k × V) → ℂ) p volume ^ 2 := by
  obtain ⟨C, hC, hdec⟩ := glyz_enlarged_dyadic_decoupling_of_admissible_square_loss
    (le_trans (by norm_num) hp) hε R
  refine ⟨C, hC, fun N f hf => ?_⟩
  apply glyz_cylindrical_square_decoupling (Finset.range (2 ^ N)) _
    (fun i _ => (isCompact_glyzFrequencyBox _ _ R).isClosed) f hf hp (by positivity)
  intro g hg
  have he : ((∑ i ∈ Finset.range (2 ^ N), g i : SchwartzMap (GlyzSpace k) ℂ) :
      GlyzSpace k → ℂ) = fun x => ∑ i ∈ Finset.range (2 ^ N), g i x := by
    ext x
    simp
  simpa only [glyzDyadicSquareEnergy, he] using hdec N g hg

theorem glyz_critical_cylindrical_moment_decoupling (k : ℕ) (hk : 0 < k)
    {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ∀ f : ℕ → SchwartzMap (WithLp 2 (GlyzSpace k × V)) ℂ,
      (∀ i ∈ Finset.range (2 ^ N),
        Function.support (𝓕 (f i : WithLp 2 (GlyzSpace k × V) → ℂ)) ⊆
          {z | (WithLp.ofLp z).1 ∈
            glyzFrequencyBox (glyzMomentFrequencyFrame k (glyzDyadicCenter N i)
              (glyzDyadicScale N) (glyzDyadicScale_pos N))
              ((EuclideanSpace.equiv (Fin k) ℝ).symm
                (glyzMomentCurve k (glyzDyadicCenter N i))) R}) →
      lpNorm ((∑ i ∈ Finset.range (2 ^ N), f i :
        SchwartzMap (WithLp 2 (GlyzSpace k × V)) ℂ) :
          WithLp 2 (GlyzSpace k × V) → ℂ) (glyzCriticalNNExponent k) volume ^ 2 ≤
        C * (2 : ℝ) ^ (ε * N) *
          ∑ i ∈ Finset.range (2 ^ N), lpNorm (f i :
            WithLp 2 (GlyzSpace k × V) → ℂ) (glyzCriticalNNExponent k) volume ^ 2 := by
  apply glyz_cylindrical_moment_decoupling_of_admissible_loss
    (p := glyzCriticalNNExponent k) ?_
    (glyz_critical_admissible_square_loss k hk hε) R
  exact two_le_glyzCriticalNNExponent hk

end PlanarNikodym
