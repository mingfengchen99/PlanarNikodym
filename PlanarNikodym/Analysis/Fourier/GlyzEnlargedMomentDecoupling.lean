import PlanarNikodym.Analysis.Fourier.GlyzMomentRadiusReduction
import PlanarNikodym.Analysis.Fourier.GlyzDyadicNestedBlocks

/-! Fixed enlargements of actual dyadic moment boxes preserve every
admissible square loss. A fixed number of generations is grouped into
standard moment boxes, and the finite triangle inequality pays only a
radius-dependent constant. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform BigOperators NNReal ENNReal
namespace PlanarNikodym

private theorem glyz_schwartz_sum_coe (m : ℕ) (I : Finset ℕ)
    (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) :
    ((∑ i ∈ I, f i : SchwartzMap (GlyzSpace m) ℂ) : GlyzSpace m → ℂ) =
      fun x => ∑ i ∈ I, f i x := by
  ext x
  simp

/-- Actual Fourier supports in dyadic moment boxes of radius `R`. -/
def GlyzDyadicEnlargedSupported (m N : ℕ) (R : ℝ)
    (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) : Prop :=
  ∀ i ∈ Finset.range (2 ^ N),
    Function.support (𝓕 (f i : GlyzSpace m → ℂ)) ⊆
      glyzFrequencyBox (glyzMomentFrequencyFrame m (glyzDyadicCenter N i)
        (glyzDyadicScale N) (glyzDyadicScale_pos N))
        ((EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m (glyzDyadicCenter N i))) R

/-- Grouping `q` generations costs at most `2 ^ q` in square energy.
No Fourier support assumption is needed for this finite inequality. -/
theorem glyz_dyadic_grouped_square_energy_le (m n q : ℕ) (p : ℝ≥0) (hp : 1 ≤ p)
    (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) :
    glyzDyadicSquareEnergy m n p (glyzDyadicBlock f (n + q) n) ≤
      (2 : ℝ) ^ q * glyzDyadicSquareEnergy m (n + q) p f := by
  have hblock (i : ℕ) :
      lpNorm ((glyzDyadicBlock f (n + q) n i : SchwartzMap (GlyzSpace m) ℂ) :
        GlyzSpace m → ℂ) p volume ^ (2 : ℕ) ≤
        (2 : ℝ) ^ q * glyzDyadicBlock (fun j => lpNorm (f j) p volume ^ (2 : ℕ))
          (n + q) n i := by
    have h := glyz_schwartz_dyadic_square_le_trivial m q p hp
      (fun j => f (i * 2 ^ q + j))
    simpa only [glyzDyadicBlock, Nat.add_sub_cancel_left, glyzDyadicSquareEnergy,
      glyz_schwartz_sum_coe] using h
  unfold glyzDyadicSquareEnergy
  calc
    _ ≤ ∑ i ∈ Finset.range (2 ^ n), (2 : ℝ) ^ q *
        glyzDyadicBlock (fun j => lpNorm (f j) p volume ^ (2 : ℕ)) (n + q) n i :=
      Finset.sum_le_sum fun i _ => hblock i
    _ = (2 : ℝ) ^ q * ∑ i ∈ Finset.range (2 ^ (n + q)),
        lpNorm (f i) p volume ^ (2 : ℕ) := by
      rw [← Finset.mul_sum, glyz_sum_dyadic_blocks _ _ _ (Nat.le_add_right n q)]

/-- Once the geometric radius reduction holds at `q`, the actual
Schwartz block family has standard moment-box Fourier support. -/
theorem glyz_dyadic_enlarged_grouped_supported (m q : ℕ) (R : ℝ)
    (hgeo : ∀ n i j : ℕ, j < 2 ^ q →
      glyzFrequencyBox (glyzMomentFrequencyFrame m
        (glyzDyadicCenter (n + q) (i * 2 ^ q + j)) (glyzDyadicScale (n + q))
        (glyzDyadicScale_pos (n + q)))
        ((EuclideanSpace.equiv (Fin m) ℝ).symm
          (glyzMomentCurve m (glyzDyadicCenter (n + q) (i * 2 ^ q + j)))) R ⊆
      glyzMomentFrequencyBox m (glyzDyadicCenter n i) (glyzDyadicScale n)
        (glyzDyadicScale_pos n))
    (n : ℕ) (f : ℕ → SchwartzMap (GlyzSpace m) ℂ)
    (hf : GlyzDyadicEnlargedSupported m (n + q) R f) :
    GlyzDyadicSupported m n (glyzDyadicBlock f (n + q) n) := by
  classical
  intro i hi ξ hξ
  by_contra hout
  have hz (j : ℕ) (hj : j < 2 ^ q) :
      𝓕 (f (i * 2 ^ q + j) : GlyzSpace m → ℂ) ξ = 0 := by
    by_contra hjz
    exact hout (hgeo n i j hj (hf _
      (Finset.mem_range.mpr (glyz_dyadic_descendant_lt (Finset.mem_range.mp hi) hj)) hjz))
  apply hξ
  change (𝓕 (∑ j ∈ Finset.range (2 ^ ((n + q) - n)),
    f (i * 2 ^ ((n + q) - n) + j) : SchwartzMap (GlyzSpace m) ℂ)) ξ = 0
  simp only [Nat.add_sub_cancel_left, FourierTransform.fourier_sum, sum_apply]
  exact Finset.sum_eq_zero fun j hj => hz j (Finset.mem_range.mp hj)

/-- Every feasible loss for the actual radius-one optimal constants
holds for every fixed enlargement, with one coefficient chosen before
the depth and the test family. The radius reduction is proved geometry,
not a new analytic decoupling hypothesis. -/
theorem glyz_enlarged_dyadic_decoupling_of_admissible_square_loss
    {m : ℕ} {p : ℝ≥0} (hp : 1 ≤ p) {a : ℝ}
    (ha : GlyzAdmissibleSquareLoss m p a) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ f : ℕ → SchwartzMap (GlyzSpace m) ℂ,
      GlyzDyadicEnlargedSupported m N R f →
      lpNorm (fun x => ∑ i ∈ Finset.range (2 ^ N), f i x) p volume ^ (2 : ℕ) ≤
        C * (2 : ℝ) ^ (a * N) * glyzDyadicSquareEnergy m N p f := by
  obtain ⟨q, hgeo⟩ := exists_glyz_dyadic_radius_reduction m R
  obtain ⟨C, hC, hdec⟩ := glyz_dyadic_decoupling_of_admissible_square_loss hp ha
  refine ⟨max C 1 * (2 : ℝ) ^ q, mul_pos (lt_of_lt_of_le hC (le_max_left _ _))
    (by positivity), fun N f hf => ?_⟩
  have hE := glyzDyadicSquareEnergy_nonneg m N p f
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (a * N) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg ha.1 (Nat.cast_nonneg N))
  by_cases hq : q ≤ N
  · let n := N - q
    have he : n + q = N := Nat.sub_add_cancel hq
    have hfs : GlyzDyadicEnlargedSupported m (n + q) R f := by simpa only [he] using hf
    have hs := glyz_dyadic_enlarged_grouped_supported m q R hgeo n f hfs
    have h := hdec n (glyzDyadicBlock f (n + q) n) hs
    have hsum : (fun x => ∑ i ∈ Finset.range (2 ^ n),
        (glyzDyadicBlock f (n + q) n i : SchwartzMap (GlyzSpace m) ℂ) x) =
        (fun x => ∑ i ∈ Finset.range (2 ^ N), f i x) := by
      funext x
      have ht := congrArg (fun g : SchwartzMap (GlyzSpace m) ℂ => g x)
        (glyz_sum_dyadic_blocks f (n + q) n (Nat.le_add_right n q))
      simpa only [sum_apply, he] using ht
    rw [hsum] at h
    have henergy := glyz_dyadic_grouped_square_energy_le m n q p hp f
    rw [he] at henergy
    have hscale : (2 : ℝ) ^ (a * (n : ℝ)) ≤ (2 : ℝ) ^ (a * (N : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le N q) ha.1)
    calc
      _ ≤ C * (2 : ℝ) ^ (a * n) * glyzDyadicSquareEnergy m n p
          (glyzDyadicBlock f (n + q) n) := h
      _ ≤ C * (2 : ℝ) ^ (a * n) * ((2 : ℝ) ^ q * glyzDyadicSquareEnergy m N p f) :=
        mul_le_mul_of_nonneg_left (by simpa only [he] using henergy) (by positivity)
      _ ≤ max C 1 * (2 : ℝ) ^ (a * N) * ((2 : ℝ) ^ q * glyzDyadicSquareEnergy m N p f) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (le_max_left C 1) hscale (by positivity)
            (le_trans hC.le (le_max_left C 1))) (mul_nonneg (by positivity) hE)
      _ = _ := by ring
  · apply (glyz_schwartz_dyadic_square_le_trivial m N p hp f).trans
    apply mul_le_mul_of_nonneg_right _ hE
    calc
      (2 : ℝ) ^ N ≤ (2 : ℝ) ^ q := pow_le_pow_right₀ (by norm_num) (by omega)
      _ ≤ (max C 1 * (2 : ℝ) ^ (a * N)) * (2 : ℝ) ^ q :=
        le_mul_of_one_le_left (by positivity)
          (one_le_mul_of_one_le_of_one_le (le_max_right C 1) hpow)
      _ = _ := by ring

/-- Exponents strictly above the optimal radius-one loss are valid for
all fixed radii, including radii created by uncertainty localization. -/
theorem glyz_enlarged_dyadic_decoupling_of_optimal_lt
    (m : ℕ) (p : ℝ≥0) (hp : 1 ≤ p) {a : ℝ}
    (ha : glyzOptimalSquareLoss m p < a) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ f : ℕ → SchwartzMap (GlyzSpace m) ℂ,
      GlyzDyadicEnlargedSupported m N R f →
      lpNorm (fun x => ∑ i ∈ Finset.range (2 ^ N), f i x) p volume ^ (2 : ℕ) ≤
        C * (2 : ℝ) ^ (a * N) * glyzDyadicSquareEnergy m N p f :=
  glyz_enlarged_dyadic_decoupling_of_admissible_square_loss hp
    (glyz_admissible_square_loss_of_optimal_lt m p hp ha) R

/-- Pulling an enlarged moment box back by the exact moment affine map
preserves its coefficient radius. -/
theorem glyz_moment_affine_enlarged_support (m : ℕ) (c κ s δ R : ℝ)
    (hκ : 0 < κ) (hδ : 0 < δ) (f : SchwartzMap (GlyzSpace m) ℂ)
    (hf : Function.support (𝓕 (f : GlyzSpace m → ℂ)) ⊆
      glyzFrequencyBox (glyzMomentFrequencyFrame m (c + κ * s) (κ * δ) (mul_pos hκ hδ))
        ((EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m (c + κ * s))) R) :
    Function.support (𝓕 (glyzSchwartzFrequencyAffine
      (glyzMomentAffineEuclidean m c κ hκ.ne').symm
      (-((glyzMomentAffineEuclidean m c κ hκ.ne').symm
        ((EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m c)))) f :
          GlyzSpace m → ℂ)) ⊆
      glyzFrequencyBox (glyzMomentFrequencyFrame m s δ hδ)
        ((EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m s)) R := by
  intro ξ hξ
  rw [support_fourier_glyzSchwartzFrequencyAffine] at hξ
  obtain ⟨η, hη, rfl⟩ := hξ
  have hs := hf hη
  rw [← glyzMomentFrequencyBox_affine_image_radius m c κ s δ R hκ hδ] at hs
  obtain ⟨ζ, hζ, rfl⟩ := hs
  simpa only [map_add, ContinuousLinearEquiv.symm_apply_apply, neg_add_cancel_left] using hζ

/-- The fixed-radius estimate is uniform on every translated and dilated
moment interval. In particular `c = -1/2`, `κ = 1` is the centered grid
used by the Taylor model. The exact affine determinant cancels. -/
theorem glyz_enlarged_affine_dyadic_decoupling_of_admissible_square_loss
    {m : ℕ} {p : ℝ≥0} (hp : 1 ≤ p) {a : ℝ}
    (ha : GlyzAdmissibleSquareLoss m p a) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (c κ : ℝ) (hκ : 0 < κ)
      (f : ℕ → SchwartzMap (GlyzSpace m) ℂ),
      (∀ i ∈ Finset.range (2 ^ N),
        Function.support (𝓕 (f i : GlyzSpace m → ℂ)) ⊆
          glyzFrequencyBox (glyzMomentFrequencyFrame m
            (c + κ * glyzDyadicCenter N i) (κ * glyzDyadicScale N)
            (mul_pos hκ (glyzDyadicScale_pos N)))
            ((EuclideanSpace.equiv (Fin m) ℝ).symm
              (glyzMomentCurve m (c + κ * glyzDyadicCenter N i))) R) →
      lpNorm (fun x => ∑ i ∈ Finset.range (2 ^ N), f i x) p volume ^ (2 : ℕ) ≤
        C * (2 : ℝ) ^ (a * N) * glyzDyadicSquareEnergy m N p f := by
  obtain ⟨C, hC, hdec⟩ := glyz_enlarged_dyadic_decoupling_of_admissible_square_loss hp ha R
  refine ⟨C, hC, fun N c κ hκ f hf => ?_⟩
  let L := (glyzMomentAffineEuclidean m c κ hκ.ne').symm
  let b := -L ((EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m c))
  let g := fun i => glyzSchwartzFrequencyAffine L b (f i)
  have hg : GlyzDyadicEnlargedSupported m N R g := by
    intro i hi
    exact glyz_moment_affine_enlarged_support m c κ (glyzDyadicCenter N i)
      (glyzDyadicScale N) R hκ (glyzDyadicScale_pos N) (f i) (hf i hi)
  have h := hdec N g hg
  have ht := glyz_affine_decoupling_transfer L b (Finset.range (2 ^ N)) f p
    (C * (2 : ℝ) ^ (a * N)) (by
      simpa only [glyz_schwartz_sum_coe, glyzDyadicSquareEnergy, g] using h)
  simpa only [glyz_schwartz_sum_coe, glyzDyadicSquareEnergy] using ht

/-- Centered dyadic moment boxes, with the same coefficient chosen before
the depth. This is the grid produced by expansion at a parent midpoint. -/
theorem glyz_enlarged_centered_dyadic_decoupling_of_admissible_square_loss
    {m : ℕ} {p : ℝ≥0} (hp : 1 ≤ p) {a : ℝ}
    (ha : GlyzAdmissibleSquareLoss m p a) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ f : ℕ → SchwartzMap (GlyzSpace m) ℂ,
      (∀ i ∈ Finset.range (2 ^ N),
        Function.support (𝓕 (f i : GlyzSpace m → ℂ)) ⊆
          glyzFrequencyBox (glyzMomentFrequencyFrame m
            (glyzDyadicCenter N i - 1 / 2) (glyzDyadicScale N) (glyzDyadicScale_pos N))
            ((EuclideanSpace.equiv (Fin m) ℝ).symm
              (glyzMomentCurve m (glyzDyadicCenter N i - 1 / 2))) R) →
      lpNorm (fun x => ∑ i ∈ Finset.range (2 ^ N), f i x) p volume ^ (2 : ℕ) ≤
        C * (2 : ℝ) ^ (a * N) * glyzDyadicSquareEnergy m N p f := by
  obtain ⟨C, hC, h⟩ := glyz_enlarged_affine_dyadic_decoupling_of_admissible_square_loss hp ha R
  refine ⟨C, hC, fun N f hf => h N (-1 / 2) 1 zero_lt_one f ?_⟩
  intro i hi
  simpa only [one_mul, neg_div, sub_eq_add_neg, add_comm] using hf i hi

end PlanarNikodym
