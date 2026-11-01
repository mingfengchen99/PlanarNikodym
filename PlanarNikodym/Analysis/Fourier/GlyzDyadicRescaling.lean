import PlanarNikodym.Analysis.Fourier.GlyzMomentBoxRescaling
import PlanarNikodym.Analysis.Fourier.GlyzAffineLpTransfer
import PlanarNikodym.Analysis.Fourier.GlyzDyadicWhitney

/-! Dyadic indices for the actual moment-curve Fourier boxes and the
affine rescaling of the corresponding Schwartz block sums. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform ENNReal NNReal
namespace PlanarNikodym

def glyzDyadicScale (N : ℕ) : ℝ := ((2 : ℝ) ^ N)⁻¹

def glyzDyadicCenter (N i : ℕ) : ℝ :=
  glyzDyadicScale N * ((i : ℝ) + 1 / 2)

theorem glyzDyadicScale_pos (N : ℕ) : 0 < glyzDyadicScale N := by
  unfold glyzDyadicScale
  positivity

theorem glyzDyadicScale_add (n q : ℕ) :
    glyzDyadicScale (n + q) = glyzDyadicScale n * glyzDyadicScale q := by
  simp [glyzDyadicScale, pow_add, mul_comm]

theorem glyzDyadicCenter_rescale (n q i j : ℕ) :
    glyzDyadicScale n * (i : ℝ) + glyzDyadicScale n * glyzDyadicCenter q j =
      glyzDyadicCenter (n + q) (i * 2 ^ q + j) := by
  simp only [glyzDyadicCenter, glyzDyadicScale_add, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat]
  have hq : glyzDyadicScale q * (2 : ℝ) ^ q = 1 := by
    exact inv_mul_cancel₀ (by positivity)
  calc
    _ = glyzDyadicScale n * ((i : ℝ) + glyzDyadicScale q * ((j : ℝ) + 1 / 2)) := by ring
    _ = _ := by
      conv_lhs => arg 2; arg 1; rw [← mul_one (i : ℝ), ← hq]
      ring

theorem glyzDyadicCenter_mem_Icc {N i : ℕ} (hi : i < 2 ^ N) :
    glyzDyadicCenter N i ∈ Icc (0 : ℝ) 1 := by
  have hN := glyzDyadicScale_pos N
  have hi' : (i : ℝ) + 1 ≤ (2 : ℝ) ^ N := by exact_mod_cast hi
  have he : glyzDyadicScale N * (2 : ℝ) ^ N = 1 := inv_mul_cancel₀ (by positivity)
  constructor <;> dsimp only [glyzDyadicCenter]
  · positivity
  · nlinarith

theorem glyz_dyadic_descendant_lt {n q i j : ℕ} (hi : i < 2 ^ n) (hj : j < 2 ^ q) :
    i * 2 ^ q + j < 2 ^ (n + q) := by
  rw [pow_add]
  calc
    i * 2 ^ q + j < i * 2 ^ q + 2 ^ q := Nat.add_lt_add_left hj _
    _ = (i + 1) * 2 ^ q := by ring
    _ ≤ 2 ^ n * 2 ^ q := Nat.mul_le_mul_right _ hi

theorem glyz_dyadic_moment_box_image (m n q i j : ℕ) :
    (fun ξ => (EuclideanSpace.equiv (Fin m) ℝ).symm
        (glyzMomentCurve m (glyzDyadicScale n * i)) +
      glyzMomentAffineEuclidean m (glyzDyadicScale n * i) (glyzDyadicScale n)
        (glyzDyadicScale_pos n).ne' ξ) ''
      glyzMomentFrequencyBox m (glyzDyadicCenter q j) (glyzDyadicScale q)
        (glyzDyadicScale_pos q) =
    glyzMomentFrequencyBox m (glyzDyadicCenter (n + q) (i * 2 ^ q + j))
      (glyzDyadicScale (n + q)) (glyzDyadicScale_pos (n + q)) := by
  have h :=
    glyzMomentFrequencyBox_affine_image m (glyzDyadicScale n * i)
      (glyzDyadicScale n) (glyzDyadicCenter q j) (glyzDyadicScale q)
      (glyzDyadicScale_pos n) (glyzDyadicScale_pos q)
  rw [glyzDyadicCenter_rescale] at h
  convert h using 1
  congr 2
  exact glyzDyadicScale_add n q

/-- Pull the Fourier transform back from a dyadic parent interval to
the unit interval. The phase translation is part of the actual map. -/
def glyzDyadicPullback (m n i : ℕ) (f : SchwartzMap (GlyzSpace m) ℂ) :
    SchwartzMap (GlyzSpace m) ℂ :=
  let L := glyzMomentAffineEuclidean m (glyzDyadicScale n * i) (glyzDyadicScale n)
    (glyzDyadicScale_pos n).ne'
  let a := (EuclideanSpace.equiv (Fin m) ℝ).symm
    (glyzMomentCurve m (glyzDyadicScale n * i))
  glyzSchwartzFrequencyAffine L.symm (-L.symm a) f

theorem glyzDyadicPullback_fourier_support (m n q i j : ℕ)
    (f : SchwartzMap (GlyzSpace m) ℂ)
    (hf : Function.support (𝓕 (f : GlyzSpace m → ℂ)) ⊆
      glyzMomentFrequencyBox m (glyzDyadicCenter (n + q) (i * 2 ^ q + j))
        (glyzDyadicScale (n + q)) (glyzDyadicScale_pos (n + q))) :
    Function.support (𝓕 (glyzDyadicPullback m n i f : GlyzSpace m → ℂ)) ⊆
      glyzMomentFrequencyBox m (glyzDyadicCenter q j) (glyzDyadicScale q)
        (glyzDyadicScale_pos q) := by
  intro ξ hξ
  rw [glyzDyadicPullback, support_fourier_glyzSchwartzFrequencyAffine] at hξ
  obtain ⟨η, hη, rfl⟩ := hξ
  have hs := hf hη
  rw [← glyz_dyadic_moment_box_image m n q i j] at hs
  obtain ⟨ζ, hζ, rfl⟩ := hs
  simpa only [map_add, ContinuousLinearEquiv.symm_apply_apply, neg_add_cancel_left] using hζ

/-- The actual finite dyadic block obeys any unit-scale squared
decoupling estimate at the relative depth, with exactly the same
constant. No determinant or parent-scale loss remains. -/
theorem glyz_dyadic_block_decoupling_transfer (m n q i : ℕ)
    (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) (p : ℝ≥0∞) (D : ℝ)
    (hf : ∀ j < 2 ^ q, Function.support
      (𝓕 (f (i * 2 ^ q + j) : GlyzSpace m → ℂ)) ⊆
      glyzMomentFrequencyBox m (glyzDyadicCenter (n + q) (i * 2 ^ q + j))
        (glyzDyadicScale (n + q)) (glyzDyadicScale_pos (n + q)))
    (hD : ∀ g : ℕ → SchwartzMap (GlyzSpace m) ℂ,
      (∀ j < 2 ^ q, Function.support (𝓕 (g j : GlyzSpace m → ℂ)) ⊆
        glyzMomentFrequencyBox m (glyzDyadicCenter q j) (glyzDyadicScale q)
          (glyzDyadicScale_pos q)) →
      lpNorm ((∑ j ∈ Finset.range (2 ^ q), g j : SchwartzMap (GlyzSpace m) ℂ) :
        GlyzSpace m → ℂ) p volume ^ (2 : ℕ) ≤
      D * ∑ j ∈ Finset.range (2 ^ q), lpNorm (g j : GlyzSpace m → ℂ) p volume ^ (2 : ℕ)) :
    lpNorm ((glyzDyadicBlock f (n + q) n i : SchwartzMap (GlyzSpace m) ℂ) :
      GlyzSpace m → ℂ) p volume ^ (2 : ℕ) ≤
      D * glyzDyadicBlock (fun j => lpNorm (f j : GlyzSpace m → ℂ) p volume ^ (2 : ℕ))
        (n + q) n i := by
  have h := hD (fun j => glyzDyadicPullback m n i (f (i * 2 ^ q + j)))
    (fun j hj => glyzDyadicPullback_fourier_support m n q i j _ (hf j hj))
  have ht := glyz_affine_decoupling_transfer
    (glyzMomentAffineEuclidean m (glyzDyadicScale n * i) (glyzDyadicScale n)
      (glyzDyadicScale_pos n).ne').symm
    (-((glyzMomentAffineEuclidean m (glyzDyadicScale n * i) (glyzDyadicScale n)
      (glyzDyadicScale_pos n).ne').symm
      ((EuclideanSpace.equiv (Fin m) ℝ).symm
        (glyzMomentCurve m (glyzDyadicScale n * i)))))
    (Finset.range (2 ^ q)) (fun j => f (i * 2 ^ q + j)) p D h
  simpa only [glyzDyadicBlock, Nat.add_sub_cancel_left] using ht

end PlanarNikodym
