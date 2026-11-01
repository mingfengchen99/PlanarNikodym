import PlanarNikodym.Analysis.Fourier.GlyzCurveScaleIteration
import PlanarNikodym.Analysis.Fourier.GlyzProjectedCurveNesting

/-! The actual dyadic Taylor step for projected curves. All grouped
Fourier supports are proved from the original fine pieces; the only
analytic input is a lower-dimensional moment-curve estimate. -/
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal ENNReal FourierTransform
namespace PlanarNikodym

/-- Fine Fourier support, rather than a hypothesis about the intermediate
blocks, suffices for the actual one-step norm inequality. Both the Taylor
threshold and the required moment-box radius are uniform in the dyadic
depths and in the Schwartz family. -/
theorem exists_uniform_glyzCoordinateCurve_dyadic_step
    (l r : ℕ) {ν Q : ℝ} (hν : 0 < ν) (hQ : 0 < Q) :
    ∃ ρ R : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 0 < R ∧
      ∀ (t a b : ℝ), a ∈ Set.Icc (-1 : ℝ) 1 → b ∈ Set.Icc (-1 : ℝ) 1 →
      a < b → b - a < ρ → (a, t) ∈ separatedMixedCenters ν →
      ∀ (N n m i : ℕ), n ≤ m → m ≤ N → i < 2 ^ n →
      glyzDyadicScale m ≤ b - a →
      (b - a) ^ (l + 1) ≤ glyzDyadicScale m ^ l →
      ∀ (f : ℕ → SchwartzMap (GlyzSpace l) ℂ) (p : ℝ≥0∞) (D : ℝ),
      (∀ j < 2 ^ (m - n),
        glyzDyadicCenter m (i * 2 ^ (m - n) + j) ∈ Set.Icc a b ∧
        (glyzDyadicCenter m (i * 2 ^ (m - n) + j), t) ∈ separatedMixedCenters ν) →
      (∀ j < 2 ^ N, Function.support (𝓕 (f j : GlyzSpace l → ℂ)) ⊆
        glyzEnlargedCurveBox (glyzCoordinateCurve l r t) l
          (glyzDyadicCenter N j) (glyzDyadicScale N) Q) →
      (∀ g : ℕ → SchwartzMap (GlyzSpace l) ℂ,
        (∀ j < 2 ^ (m - n), Function.support (𝓕 (g j : GlyzSpace l → ℂ)) ⊆
          glyzFrequencyBox
            (glyzMomentFrequencyFrame l
              (glyzDyadicCenter m (i * 2 ^ (m - n) + j) - a)
              (glyzDyadicScale m) (glyzDyadicScale_pos m))
            ((EuclideanSpace.equiv (Fin l) ℝ).symm
              (glyzMomentCurve l (glyzDyadicCenter m (i * 2 ^ (m - n) + j) - a))) R) →
        lpNorm ((∑ j ∈ Finset.range (2 ^ (m - n)), g j : SchwartzMap (GlyzSpace l) ℂ) :
          GlyzSpace l → ℂ) p volume ^ 2 ≤
          D * ∑ j ∈ Finset.range (2 ^ (m - n)), lpNorm (g j : GlyzSpace l → ℂ) p volume ^ 2) →
      lpNorm ((glyzDyadicBlock f N n i : SchwartzMap (GlyzSpace l) ℂ) :
        GlyzSpace l → ℂ) p volume ^ 2 ≤
        D * glyzDyadicBlock
          (fun j => lpNorm ((glyzDyadicBlock f N m j : SchwartzMap (GlyzSpace l) ℂ) :
            GlyzSpace l → ℂ) p volume ^ 2) m n i := by
  obtain ⟨B, hB, hsupport⟩ := exists_uniform_glyz_dyadic_curve_block_support l r hν hQ
  obtain ⟨ρ, R, hρ, hρ1, hR, hstep⟩ :=
    exists_uniform_glyzCoordinateCurve_enlarged_block_step l r hν hB
  refine ⟨ρ, R, hρ, hρ1, hR, fun t a b ha hb hab hshort hsep
    N n m i hnm hmN hi hδκ hscale f p D hs hf hD => ?_⟩
  apply hstep t a b ha hb hab hshort hsep
    (glyzDyadicScale m) (glyzDyadicScale_pos m) hδκ hscale
    N n m i hnm hmN
    (fun j => glyzDyadicCenter m (i * 2 ^ (m - n) + j)) f p D hs
  · intro j hj
    apply hsupport t N m (i * 2 ^ (m - n) + j) hmN
    · have he : n + (m - n) = m := Nat.add_sub_of_le hnm
      simpa only [he] using glyz_dyadic_descendant_lt hi hj
    · exact (hs j hj).2
    · exact hf
  · exact hD

end PlanarNikodym
