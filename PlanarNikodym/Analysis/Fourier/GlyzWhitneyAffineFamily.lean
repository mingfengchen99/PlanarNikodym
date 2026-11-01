import PlanarNikodym.Analysis.Fourier.GlyzAffineBilinearLp
import PlanarNikodym.Analysis.Fourier.GlyzFixedDepthBilinearLoss

/-! A Whitney window need not be a dyadic ancestor. We use its actual
left endpoint and length four times the fine parent length, with zero
padding beyond the original unit interval. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators FourierTransform NNReal ENNReal
namespace PlanarNikodym

theorem glyzDyadicScale_four (r : ℕ) :
    4 * glyzDyadicScale (r + 2) = glyzDyadicScale r := by
  simp [glyzDyadicScale, pow_add]
  ring

theorem glyz_whitney_moment_box_image (m d r i h : ℕ) :
    (fun ξ => (EuclideanSpace.equiv (Fin m) ℝ).symm
      (glyzMomentCurve m (glyzDyadicScale d * i)) +
      glyzMomentAffineEuclidean m (glyzDyadicScale d * i) (4 * glyzDyadicScale d)
        (mul_pos (by norm_num) (glyzDyadicScale_pos d)).ne' ξ) ''
      glyzMomentFrequencyBox m (glyzDyadicCenter (r + 2) h) (glyzDyadicScale (r + 2))
        (glyzDyadicScale_pos (r + 2)) =
      glyzMomentFrequencyBox m (glyzDyadicCenter (d + r) (i * 2 ^ r + h))
        (glyzDyadicScale (d + r)) (glyzDyadicScale_pos (d + r)) := by
  have hs : (4 * glyzDyadicScale d) * glyzDyadicScale (r + 2) =
      glyzDyadicScale (d + r) := by
    rw [glyzDyadicScale_add d r]
    calc
      _ = glyzDyadicScale d * (4 * glyzDyadicScale (r + 2)) := by ring
      _ = _ := by rw [glyzDyadicScale_four]
  have hc : glyzDyadicScale d * i +
      (4 * glyzDyadicScale d) * glyzDyadicCenter (r + 2) h =
      glyzDyadicCenter (d + r) (i * 2 ^ r + h) := by
    rw [← glyzDyadicCenter_rescale]
    unfold glyzDyadicCenter
    rw [show (4 * glyzDyadicScale d) * (glyzDyadicScale (r + 2) * ((h : ℝ) + 1 / 2)) =
      glyzDyadicScale d * ((4 * glyzDyadicScale (r + 2)) * ((h : ℝ) + 1 / 2)) by ring,
      glyzDyadicScale_four]
  have hi := glyzMomentFrequencyBox_affine_image m (glyzDyadicScale d * i)
    (4 * glyzDyadicScale d) (glyzDyadicCenter (r + 2) h) (glyzDyadicScale (r + 2))
    (mul_pos (by norm_num) (glyzDyadicScale_pos d)) (glyzDyadicScale_pos (r + 2))
  rw [hc] at hi
  convert hi using 1
  congr 2
  exact hs.symm

def glyzWhitneyAffine (m d i : ℕ) : GlyzSpace m ≃L[ℝ] GlyzSpace m :=
  (glyzMomentAffineEuclidean m (glyzDyadicScale d * i) (4 * glyzDyadicScale d)
    (mul_pos (by norm_num) (glyzDyadicScale_pos d)).ne').symm

def glyzWhitneyOffset (m d i : ℕ) : GlyzSpace m :=
  -glyzWhitneyAffine m d i
    ((EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m (glyzDyadicScale d * i)))

def glyzWhitneyPullback (m d i : ℕ) (f : SchwartzMap (GlyzSpace m) ℂ) :
    SchwartzMap (GlyzSpace m) ℂ :=
  glyzSchwartzFrequencyAffine (glyzWhitneyAffine m d i) (glyzWhitneyOffset m d i) f

theorem glyzWhitneyPullback_support (m d r i h : ℕ)
    (f : SchwartzMap (GlyzSpace m) ℂ)
    (hf : Function.support (𝓕 (f : GlyzSpace m → ℂ)) ⊆
      glyzMomentFrequencyBox m (glyzDyadicCenter (d + r) (i * 2 ^ r + h))
        (glyzDyadicScale (d + r)) (glyzDyadicScale_pos (d + r))) :
    Function.support (𝓕 (glyzWhitneyPullback m d i f : GlyzSpace m → ℂ)) ⊆
      glyzMomentFrequencyBox m (glyzDyadicCenter (r + 2) h)
        (glyzDyadicScale (r + 2)) (glyzDyadicScale_pos (r + 2)) := by
  intro ξ hξ
  rw [glyzWhitneyPullback, support_fourier_glyzSchwartzFrequencyAffine] at hξ
  obtain ⟨η, hη, rfl⟩ := hξ
  have hbox := hf hη
  rw [← glyz_whitney_moment_box_image m d r i h] at hbox
  obtain ⟨ζ, hζ, rfl⟩ := hbox
  simpa only [glyzWhitneyOffset, glyzWhitneyAffine, map_add,
    ContinuousLinearEquiv.symm_apply_apply, neg_add_cancel_left] using hζ

def glyzWhitneyFamily (m d r i : ℕ) (f : ℕ → SchwartzMap (GlyzSpace m) ℂ)
    (h : ℕ) : SchwartzMap (GlyzSpace m) ℂ :=
  if i * 2 ^ r + h < 2 ^ (d + r) then
    glyzWhitneyPullback m d i (f (i * 2 ^ r + h)) else 0

theorem glyzWhitneyFamily_supported (m d r i : ℕ)
    (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) (hf : GlyzDyadicSupported m (d + r) f) :
    GlyzDyadicSupported m (r + 2) (glyzWhitneyFamily m d r i f) := by
  intro h _
  unfold glyzWhitneyFamily
  split_ifs with hh
  · exact glyzWhitneyPullback_support m d r i h _ (hf _ (Finset.mem_range.mpr hh))
  · rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_zero]
    simp only [FunLike.coe_zero, Function.support_zero, empty_subset]

theorem glyzWhitneyFamily_block (m d r i k : ℕ) (hk : i + k < 2 ^ d)
    (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) :
    glyzDyadicBlock (glyzWhitneyFamily m d r i f) (r + 2) 2 k =
      glyzWhitneyPullback m d i (glyzDyadicBlock f (d + r) d (i + k)) := by
  unfold glyzDyadicBlock
  simp only [Nat.add_sub_cancel_right, Nat.add_sub_cancel_left]
  rw [glyzWhitneyPullback, glyzSchwartzFrequencyAffine_sum]
  apply Finset.sum_congr rfl
  intro h hh
  have he : i * 2 ^ r + (k * 2 ^ r + h) = (i + k) * 2 ^ r + h := by ring
  have hindex := glyz_dyadic_descendant_lt hk (Finset.mem_range.mp hh)
  simp only [glyzWhitneyFamily, he, if_pos hindex, glyzWhitneyPullback]

theorem glyzWhitneyFamily_energy (m d r i k : ℕ) (hk : i + k < 2 ^ d)
    (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) (p : ℝ≥0) :
    glyzDyadicBlock
      (fun h => lpNorm (glyzWhitneyFamily m d r i f h) p volume ^ (2 : ℕ)) (r + 2) 2 k =
      glyzAffineLpFactor (glyzWhitneyAffine m d i) p ^ (2 : ℕ) *
        glyzDyadicBlock (fun h => lpNorm (f h) p volume ^ (2 : ℕ)) (d + r) d (i + k) := by
  unfold glyzDyadicBlock
  simp only [Nat.add_sub_cancel_right, Nat.add_sub_cancel_left]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  have he : i * 2 ^ r + (k * 2 ^ r + h) = (i + k) * 2 ^ r + h := by ring
  have hindex := glyz_dyadic_descendant_lt hk (Finset.mem_range.mp hh)
  simp only [glyzWhitneyFamily, he, if_pos hindex, glyzWhitneyPullback,
    lpNorm_glyzSchwartzFrequencyAffine, mul_pow]

end PlanarNikodym
