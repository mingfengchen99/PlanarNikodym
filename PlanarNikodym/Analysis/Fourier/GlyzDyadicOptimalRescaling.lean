import PlanarNikodym.Analysis.Fourier.GlyzDyadicRescaling
import PlanarNikodym.Analysis.Fourier.GlyzDecouplingConstants

/-! GLYZ affine rescaling with the actual optimal dyadic constants.
The parent block and its energy are sums of the original finest pieces. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform ENNReal NNReal
namespace PlanarNikodym

theorem glyz_dyadic_block_le_optimal_constant (m N n i : ℕ)
    (hn : n ≤ N) (hi : i < 2 ^ n) (p : ℝ≥0) (hp : 1 ≤ p)
    (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) (hf : GlyzDyadicSupported m N f) :
    lpNorm ((glyzDyadicBlock f N n i : SchwartzMap (GlyzSpace m) ℂ) :
      GlyzSpace m → ℂ) p volume ^ (2 : ℕ) ≤
      glyzDyadicSquareConstant m (N - n) p *
        glyzDyadicBlock (fun j => lpNorm (f j : GlyzSpace m → ℂ) p volume ^ (2 : ℕ)) N n i := by
  have he : n + (N - n) = N := Nat.add_sub_of_le hn
  have h := glyz_dyadic_block_decoupling_transfer m n (N - n) i f p
    (glyzDyadicSquareConstant m (N - n) p)
    (fun j hj => by
      have hidx := glyz_dyadic_descendant_lt hi hj
      rw [he] at hidx
      convert hf (i * 2 ^ (N - n) + j) (Finset.mem_range.mpr hidx) using 1
      simp only [glyzDyadicCenter, glyzDyadicScale]
      congr 1 <;> simp only [he])
    (fun g hg => by
      have hs : GlyzDyadicSupported m (N - n) g := by
        intro j hj
        exact hg j (Finset.mem_range.mp hj)
      have hD := (glyzDyadicSquareConstant_bound m (N - n) p hp).2 g hs
      have hsum : ((∑ j ∈ Finset.range (2 ^ (N - n)), g j :
          SchwartzMap (GlyzSpace m) ℂ) : GlyzSpace m → ℂ) =
          fun x => ∑ j ∈ Finset.range (2 ^ (N - n)), g j x := by ext x; simp
      simpa only [glyzDyadicSquareEnergy, hsum] using hD)
  simpa only [he] using h

/-- A uniform feasible loss gives the expected relative-depth exponent
for every actual parent interval, without a new parent-dependent
constant. -/
theorem glyz_dyadic_blocks_of_admissible_square_loss {m : ℕ} {p : ℝ≥0}
    (hp : 1 ≤ p) {a : ℝ} (ha : GlyzAdmissibleSquareLoss m p a) :
    ∃ C : ℝ, 0 < C ∧ ∀ N n i : ℕ, n ≤ N → i < 2 ^ n →
      ∀ f : ℕ → SchwartzMap (GlyzSpace m) ℂ, GlyzDyadicSupported m N f →
      lpNorm ((glyzDyadicBlock f N n i : SchwartzMap (GlyzSpace m) ℂ) :
        GlyzSpace m → ℂ) p volume ^ (2 : ℕ) ≤
        C * (2 : ℝ) ^ (a * (N - n)) *
          glyzDyadicBlock (fun j => lpNorm (f j : GlyzSpace m → ℂ) p volume ^ (2 : ℕ)) N n i := by
  obtain ⟨_, C, hC, h⟩ := ha
  refine ⟨C, hC, fun N n i hn hi f hf => ?_⟩
  apply (glyz_dyadic_block_le_optimal_constant m N n i hn hi p hp f hf).trans
  apply mul_le_mul_of_nonneg_right (by simpa only [Nat.cast_sub hn] using h (N - n))
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)

end PlanarNikodym
