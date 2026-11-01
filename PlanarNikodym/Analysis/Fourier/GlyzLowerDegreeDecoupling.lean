import PlanarNikodym.Analysis.Fourier.GlyzSliceLocalDecoupling
import PlanarNikodym.Analysis.Fourier.GlyzEnlargedLowerDegreeAssembly

/-! The actual lower-degree weighted decoupling inequality.  The
transverse local estimate is supplied by lower-dimensional moment
zero loss, with no additional decoupling assumption. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped FourierTransform ENNReal NNReal BigOperators
namespace PlanarNikodym

theorem exists_uniform_glyz_lower_degree_decoupling
    (l r A : ℕ) (hr : 0 < r) (hA : l + r < A)
    (hQ : (l + r) * (l + r + 1) / 2 ≤ A)
    (p : ℝ≥0) (hp : 2 ≤ p) (hη : glyzOptimalSquareLoss l p = 0)
    (L : ℝ) (hL : 0 < L) {ν R ε : ℝ}
    (hν : 0 < ν) (hR : 0 < R) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (t : ℝ), t ∈ Icc (-1 : ℝ) 1 →
      ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      δ ^ (r + 1) ≤ L * glyzDyadicScale N ^ l →
      ∀ (g : SchwartzMap (GlyzSpace (l + r)) ℂ) (q c κ : ℝ) (hκ : 0 < κ)
      (I : Finset ℕ) (f : ℕ → SchwartzMap (GlyzSpace (l + r)) ℂ),
      I ⊆ Finset.range (2 ^ N) →
      (∀ j ∈ I, (glyzDyadicCenter N j, t) ∈ separatedMixedCenters ν) →
      (∀ j ∈ I, |glyzDyadicCenter N j - c| ≤ κ ∧ glyzDyadicScale N ≤ κ) →
      (∀ j ∈ I, Function.support (𝓕 (f j : GlyzSpace (l + r) → ℂ)) ⊆
        glyzFrequencyBox
          (glyzMomentFrequencyFrame (l + r) (glyzDyadicCenter N j)
            (glyzDyadicScale N) (glyzDyadicScale_pos N))
          ((EuclideanSpace.equiv (Fin (l + r)) ℝ).symm
            (glyzMomentCurve (l + r) (glyzDyadicCenter N j))) R) →
      let σ := glyzPolarMeasure A (glyzMomentFrequencyFrame (l + r) c κ hκ)
      let σ' := fun j => glyzPolarMeasure A
        (glyzMomentFrequencyFrame (l + r) (glyzDyadicCenter N j)
          (glyzDyadicScale N) (glyzDyadicScale_pos N))
      let G := glyzPowerAverage
        (glyzPolarMeasure A (glyzMomentFrequencyFrame (l + r) t δ hδ)) g q
      (∫⁻ x, glyzPowerAverage σ (∑ j ∈ I, f j : SchwartzMap (GlyzSpace (l + r)) ℂ)
        (p : ℝ) x * G x) ≤
      ENNReal.ofReal (C * (2 : ℝ) ^ (ε * N)) *
        (∑ j ∈ I, (∫⁻ x, glyzPowerAverage (σ' j) (f j) (p : ℝ) x * G x) ^
          (2 / (p : ℝ))) ^ ((p : ℝ) / 2) := by
  obtain ⟨B, hB, hlocal⟩ := exists_uniform_glyz_slice_local_decoupling l r (A + (l + r))
    (show 1 ≤ p by linarith) hη L hL hν hR hε
  obtain ⟨K, hK, hassembly⟩ := exists_uniform_glyz_enlarged_lower_degree_assembly
    l r A hr hA hQ p hp R hR
  refine ⟨K * B, mul_pos hK hB,
    fun N t ht δ hδ hδ1 hscale g q c κ hκ I f hI hsep hnested hf => ?_⟩
  have h := hassembly t ht δ hδ hδ1 g q c κ hκ ℕ I
    (glyzDyadicCenter N) (fun _ => glyzDyadicScale N) (fun _ => glyzDyadicScale_pos N)
    hnested f hf (B * (2 : ℝ) ^ (ε * N)) (by positivity)
    (hlocal N t (δ ^ (r + 1)) (pow_pos hδ _) hscale I f hI hsep hf)
  simpa only [mul_assoc] using h

end PlanarNikodym
