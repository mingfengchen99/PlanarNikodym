import PlanarNikodym.Analysis.Fourier.GlyzLowerDegreeDecoupling
import PlanarNikodym.Analysis.Fourier.GlyzDyadicBlockSupport
import PlanarNikodym.Analysis.Fourier.GlyzAsymmetricConstants
import PlanarNikodym.Analysis.Fourier.GlyzDyadicNestedBlocks

/-! GLYZ lower-degree decoupling applied to the actual dyadic block
sums of one finest-scale family. All Fourier support, separation and
refinement requirements are established from the original pieces. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped FourierTransform ENNReal NNReal BigOperators
namespace PlanarNikodym

theorem glyzDyadicSeparated_mem_separatedMixedCenters {n n' i j : ℕ}
    (hi : i < 2 ^ n) (hj : j < 2 ^ n') (hs : GlyzDyadicSeparated n n' i j) :
    (glyzDyadicCenter n i, glyzDyadicCenter n' j) ∈ separatedMixedCenters (1 / 4) := by
  have hi' := glyzDyadicCenter_mem_Icc hi
  have hj' := glyzDyadicCenter_mem_Icc hj
  refine ⟨⟨by linarith [hi'.1], hi'.2⟩, ⟨by linarith [hj'.1], hj'.2⟩, ?_⟩
  have hn := glyzDyadicScale_pos n
  have hn' := glyzDyadicScale_pos n'
  unfold GlyzDyadicSeparated at hs
  linarith

theorem exists_uniform_glyz_dyadic_lower_degree
    (l r A : ℕ) (hr : 0 < r) (hA : l + r < A)
    (hQ : (l + r) * (l + r + 1) / 2 ≤ A)
    (p : ℝ≥0) (hp : 2 ≤ p) (hη : glyzOptimalSquareLoss l p = 0)
    (L : ℝ) (hL : 0 < L) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N n m nb : ℕ), n ≤ m → m ≤ N → nb ≤ N →
      glyzDyadicScale nb ^ (r + 1) ≤ L * glyzDyadicScale m ^ l →
      ∀ (f : ℕ → SchwartzMap (GlyzSpace (l + r)) ℂ), GlyzDyadicSupported (l + r) N f →
      ∀ i < 2 ^ n, ∀ j < 2 ^ nb, GlyzDyadicSeparated n nb i j → ∀ q : ℝ,
      glyzWeightedBilinear (glyzDyadicPolarMeasure (l + r) A n i)
        (glyzDyadicPolarMeasure (l + r) A nb j)
        (glyzDyadicBlock f N n i : SchwartzMap (GlyzSpace (l + r)) ℂ)
        (glyzDyadicBlock f N nb j : SchwartzMap (GlyzSpace (l + r)) ℂ) (p : ℝ) q ≤
      ENNReal.ofReal (C * (2 : ℝ) ^ (ε * m)) *
        (∑ u ∈ Finset.range (2 ^ (m - n)),
          (glyzWeightedBilinear
            (glyzDyadicPolarMeasure (l + r) A m (i * 2 ^ (m - n) + u))
            (glyzDyadicPolarMeasure (l + r) A nb j)
            (glyzDyadicBlock f N m (i * 2 ^ (m - n) + u) : SchwartzMap (GlyzSpace (l + r)) ℂ)
            (glyzDyadicBlock f N nb j : SchwartzMap (GlyzSpace (l + r)) ℂ) (p : ℝ) q) ^
          (2 / (p : ℝ))) ^ ((p : ℝ) / 2) := by
  classical
  obtain ⟨R, hR, hsupport⟩ := exists_uniform_glyz_dyadic_block_support (l + r)
  obtain ⟨C, hC, hdec⟩ := exists_uniform_glyz_lower_degree_decoupling
    l r A hr hA hQ p hp hη L hL (ν := 1 / 4) (by norm_num) hR hε
  refine ⟨C, hC, fun N n m nb hnm hmN _hnbN hscale f hf i hi j hj hs q => ?_⟩
  let I : Finset ℕ := (Finset.range (2 ^ (m - n))).image (fun u => i * 2 ^ (m - n) + u)
  let g : ℕ → SchwartzMap (GlyzSpace (l + r)) ℂ := fun u => glyzDyadicBlock f N m u
  have he : n + (m - n) = m := Nat.add_sub_of_le hnm
  have hindex (u : ℕ) (hu : u < 2 ^ (m - n)) : i * 2 ^ (m - n) + u < 2 ^ m := by
    simpa only [he] using glyz_dyadic_descendant_lt hi hu
  have hI : I ⊆ Finset.range (2 ^ m) := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact Finset.mem_range.mpr (hindex v (Finset.mem_range.mp hv))
  have hsep : ∀ u ∈ I, (glyzDyadicCenter m u, glyzDyadicCenter nb j) ∈
      separatedMixedCenters (1 / 4) := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    have hd := glyzDyadicCenter_descendant_dist (n := n) (i := i) (Finset.mem_range.mp hv)
    rw [he] at hd
    have ht := abs_sub_le (glyzDyadicCenter n i)
      (glyzDyadicCenter m (i * 2 ^ (m - n) + v)) (glyzDyadicCenter nb j)
    rw [abs_sub_comm (glyzDyadicCenter n i)
      (glyzDyadicCenter m (i * 2 ^ (m - n) + v))] at ht
    have hsp : GlyzDyadicSeparated m nb (i * 2 ^ (m - n) + v) j := by
      unfold GlyzDyadicSeparated at hs ⊢
      linarith
    exact glyzDyadicSeparated_mem_separatedMixedCenters
      (hindex v (Finset.mem_range.mp hv)) hj hsp
  have hnested : ∀ u ∈ I, |glyzDyadicCenter m u - glyzDyadicCenter n i| ≤ glyzDyadicScale n ∧
      glyzDyadicScale m ≤ glyzDyadicScale n := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    have hd := glyzDyadicCenter_descendant_dist (n := n) (i := i) (Finset.mem_range.mp hv)
    rw [he] at hd
    have hn := glyzDyadicScale_pos n
    have hm := glyzDyadicScale_pos m
    constructor
    · linarith
    · linarith [abs_nonneg (glyzDyadicCenter m (i * 2 ^ (m - n) + v) - glyzDyadicCenter n i)]
  have ht : glyzDyadicCenter nb j ∈ Icc (-1 : ℝ) 1 := by
    have hh := glyzDyadicCenter_mem_Icc hj
    exact ⟨by linarith [hh.1], hh.2⟩
  have hδ1 : glyzDyadicScale nb ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have h := hdec m (glyzDyadicCenter nb j) ht (glyzDyadicScale nb)
    (glyzDyadicScale_pos nb) hδ1 hscale
    (glyzDyadicBlock f N nb j) q (glyzDyadicCenter n i) (glyzDyadicScale n)
    (glyzDyadicScale_pos n) I g hI hsep hnested
    (fun u hu => hsupport N m u hmN (Finset.mem_range.mp (hI hu)) f hf)
  have hsum : (∑ u ∈ I, g u) = glyzDyadicBlock f N n i := by
    rw [glyzDyadicBlock_refine f N n (m - n) i (by omega), he]
    unfold I
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact Nat.add_left_cancel hab
  dsimp only at h
  rw [hsum] at h
  change glyzWeightedBilinear _ _ _ _ _ _ ≤
    ENNReal.ofReal (C * (2 : ℝ) ^ (ε * m)) * (∑ u ∈ I, _) ^ ((p : ℝ) / 2) at h
  simpa only [I, Finset.sum_image (fun a _ b _ hab => Nat.add_left_cancel hab), g,
    glyzDyadicPolarMeasure, glyzWeightedBilinear] using h

end PlanarNikodym
