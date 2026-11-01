import PlanarNikodym.Analysis.Fourier.GlyzEnlargedTaylorDecoupling
import PlanarNikodym.Analysis.Fourier.GlyzDyadicNestedBlocks
import PlanarNikodym.Analysis.Fourier.GlyzDecouplingConstants

/-! Exact finite scale iteration for actual dyadic Schwartz sums.
All functions appearing at intermediate scales are constructed by grouping
the original finest pieces. The one-step estimates still have to be
supplied by the enlarged moment-box Taylor transfer. -/
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal ENNReal FourierTransform
namespace PlanarNikodym

/-- Every coarse norm energy is the sum of the actual parent energies. -/
def glyzCurveScaleEnergy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : ℕ → SchwartzMap E ℂ) (N n : ℕ) (p : ℝ≥0∞) : ℝ :=
  ∑ i ∈ Finset.range (2 ^ n),
    lpNorm ((glyzDyadicBlock f N n i : SchwartzMap E ℂ) : E → ℂ) p volume ^ 2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem glyzCurveScaleEnergy_nonneg (f : ℕ → SchwartzMap E ℂ) (N n : ℕ) (p : ℝ≥0∞) :
    0 ≤ glyzCurveScaleEnergy f N n p := Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Sum the genuine parent estimates and cancel the grouping exactly.
There is no cardinality loss at a refinement step. -/
theorem glyzCurveScaleEnergy_step (f : ℕ → SchwartzMap E ℂ)
    (N n m : ℕ) (hnm : n ≤ m) (p : ℝ≥0∞) (D : ℝ)
    (hstep : ∀ i < 2 ^ n,
      lpNorm ((glyzDyadicBlock f N n i : SchwartzMap E ℂ) : E → ℂ) p volume ^ 2 ≤
        D * glyzDyadicBlock
          (fun j => lpNorm ((glyzDyadicBlock f N m j : SchwartzMap E ℂ) : E → ℂ) p volume ^ 2) m n i) :
    glyzCurveScaleEnergy f N n p ≤ D * glyzCurveScaleEnergy f N m p := by
  unfold glyzCurveScaleEnergy
  calc
    _ ≤ ∑ i ∈ Finset.range (2 ^ n), D * glyzDyadicBlock
        (fun j => lpNorm ((glyzDyadicBlock f N m j : SchwartzMap E ℂ) : E → ℂ) p volume ^ 2) m n i :=
      Finset.sum_le_sum fun i hi => hstep i (Finset.mem_range.mp hi)
    _ = _ := by rw [← Finset.mul_sum, glyz_sum_dyadic_blocks _ m n hnm]

/-- A fixed finite number of genuine dyadic refinement estimates
multiplies the constants, with exact finest-piece energy at the end. -/
theorem glyzCurveScaleEnergy_iterate (f : ℕ → SchwartzMap E ℂ)
    (N M : ℕ) (n : ℕ → ℕ) (p : ℝ≥0∞) (D : ℕ → ℝ)
    (hmono : ∀ j < M, n j ≤ n (j + 1))
    (hD : ∀ j < M, 0 ≤ D j)
    (hstep : ∀ j < M, ∀ i < 2 ^ n j,
      lpNorm ((glyzDyadicBlock f N (n j) i : SchwartzMap E ℂ) : E → ℂ) p volume ^ 2 ≤
        D j * glyzDyadicBlock
          (fun k => lpNorm ((glyzDyadicBlock f N (n (j + 1)) k : SchwartzMap E ℂ) : E → ℂ) p volume ^ 2)
          (n (j + 1)) (n j) i) :
    glyzCurveScaleEnergy f N (n 0) p ≤
      (∏ j ∈ Finset.range M, D j) * glyzCurveScaleEnergy f N (n M) p := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hprev := ih (fun j hj => hmono j (by omega)) (fun j hj => hD j (by omega))
      (fun j hj => hstep j (by omega))
    have hnext := glyzCurveScaleEnergy_step f N (n M) (n (M + 1)) (hmono M (by omega))
      p (D M) (hstep M (by omega))
    have hprod : 0 ≤ ∏ j ∈ Finset.range M, D j := Finset.prod_nonneg fun j hj =>
      hD j (by simpa only [Finset.mem_range] using (Finset.mem_range.mp hj).trans (Nat.lt_succ_self M))
    calc
      _ ≤ (∏ j ∈ Finset.range M, D j) * glyzCurveScaleEnergy f N (n M) p := hprev
      _ ≤ (∏ j ∈ Finset.range M, D j) * (D M * glyzCurveScaleEnergy f N (n (M + 1)) p) :=
        mul_le_mul_of_nonneg_left hnext hprod
      _ = _ := by rw [Finset.prod_range_succ]; ring

/-- Exact final energy when the iteration reaches the finest scale. -/
theorem glyzCurveScaleEnergy_finest (f : ℕ → SchwartzMap E ℂ) (N : ℕ) (p : ℝ≥0∞) :
    glyzCurveScaleEnergy f N N p =
      ∑ i ∈ Finset.range (2 ^ N), lpNorm (f i : E → ℂ) p volume ^ 2 := by
  simp only [glyzCurveScaleEnergy, glyzDyadicBlock_finest]

/-- The fixed-depth iteration bound for the original finest pieces,
including the initial trivial decoupling loss. -/
theorem glyz_curve_finite_iteration (l N M : ℕ) (f : ℕ → SchwartzMap (GlyzSpace l) ℂ)
    (n : ℕ → ℕ) (hn0 : n 0 ≤ N) (hnM : n M = N)
    (p : ℝ≥0) (hp : 1 ≤ p) (D : ℕ → ℝ)
    (hmono : ∀ j < M, n j ≤ n (j + 1)) (hD : ∀ j < M, 0 ≤ D j)
    (hstep : ∀ j < M, ∀ i < 2 ^ n j,
      lpNorm ((glyzDyadicBlock f N (n j) i : SchwartzMap (GlyzSpace l) ℂ) : GlyzSpace l → ℂ) p volume ^ 2 ≤
        D j * glyzDyadicBlock
          (fun k => lpNorm ((glyzDyadicBlock f N (n (j + 1)) k : SchwartzMap (GlyzSpace l) ℂ) : GlyzSpace l → ℂ) p volume ^ 2)
          (n (j + 1)) (n j) i) :
    lpNorm ((∑ i ∈ Finset.range (2 ^ N), f i : SchwartzMap (GlyzSpace l) ℂ) :
      GlyzSpace l → ℂ) p volume ^ 2 ≤
      ((2 : ℝ) ^ n 0 * ∏ j ∈ Finset.range M, D j) *
        ∑ i ∈ Finset.range (2 ^ N), lpNorm (f i : GlyzSpace l → ℂ) p volume ^ 2 := by
  have hinit := glyz_schwartz_dyadic_square_le_trivial l (n 0) p hp (glyzDyadicBlock f N (n 0))
  have hfun : (fun x => ∑ i ∈ Finset.range (2 ^ n 0), glyzDyadicBlock f N (n 0) i x) =
      ((∑ i ∈ Finset.range (2 ^ N), f i : SchwartzMap (GlyzSpace l) ℂ) : GlyzSpace l → ℂ) := by
    ext x
    have h := congrArg (fun F : SchwartzMap (GlyzSpace l) ℂ => F x)
      (glyz_sum_dyadic_blocks f N (n 0) hn0)
    simpa only [sum_apply] using h
  rw [hfun] at hinit
  change _ ≤ (2 : ℝ) ^ n 0 * glyzCurveScaleEnergy f N (n 0) p at hinit
  have hit := glyzCurveScaleEnergy_iterate f N M n p D hmono hD hstep
  rw [hnM, glyzCurveScaleEnergy_finest] at hit
  calc
    _ ≤ (2 : ℝ) ^ n 0 * glyzCurveScaleEnergy f N (n 0) p := hinit
    _ ≤ (2 : ℝ) ^ n 0 * ((∏ j ∈ Finset.range M, D j) *
        ∑ i ∈ Finset.range (2 ^ N), lpNorm (f i : GlyzSpace l → ℂ) p volume ^ 2) :=
      mul_le_mul_of_nonneg_left hit (by positivity)
    _ = _ := by ring

/-- A parent of actual finest Schwartz pieces satisfies the Taylor
one-step estimate as soon as its grouped children have the certified
curve-box supports. The only analytic assumption is the enlarged
moment-box estimate for those child centers. -/
theorem exists_uniform_glyzCoordinateCurve_block_step
    (l r : ℕ) {ν : ℝ} (hν : 0 < ν) :
    ∃ ρ R : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 0 < R ∧
      ∀ (t a b : ℝ), a ∈ Set.Icc (-1 : ℝ) 1 → b ∈ Set.Icc (-1 : ℝ) 1 →
      a < b → b - a < ρ → (a, t) ∈ separatedMixedCenters ν →
      ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ b - a → (b - a) ^ (l + 1) ≤ δ ^ l →
      ∀ (N n m i : ℕ), n ≤ m → m ≤ N →
      ∀ (s : ℕ → ℝ) (f : ℕ → SchwartzMap (GlyzSpace l) ℂ) (p : ℝ≥0∞) (D : ℝ),
      (∀ j < 2 ^ (m - n), s j ∈ Set.Icc a b ∧ (s j, t) ∈ separatedMixedCenters ν) →
      (∀ j < 2 ^ (m - n), Function.support (𝓕
        ((glyzDyadicBlock f N m (i * 2 ^ (m - n) + j) : SchwartzMap (GlyzSpace l) ℂ) : GlyzSpace l → ℂ)) ⊆
          glyzCurveBox (glyzCoordinateCurve l r t) l (s j) δ) →
      (∀ g : ℕ → SchwartzMap (GlyzSpace l) ℂ,
        (∀ j < 2 ^ (m - n), Function.support (𝓕 (g j : GlyzSpace l → ℂ)) ⊆
          glyzFrequencyBox (glyzMomentFrequencyFrame l (s j - a) δ hδ)
            ((EuclideanSpace.equiv (Fin l) ℝ).symm (glyzMomentCurve l (s j - a))) R) →
        lpNorm ((∑ j ∈ Finset.range (2 ^ (m - n)), g j : SchwartzMap (GlyzSpace l) ℂ) :
          GlyzSpace l → ℂ) p volume ^ 2 ≤
          D * ∑ j ∈ Finset.range (2 ^ (m - n)), lpNorm (g j : GlyzSpace l → ℂ) p volume ^ 2) →
      lpNorm ((glyzDyadicBlock f N n i : SchwartzMap (GlyzSpace l) ℂ) : GlyzSpace l → ℂ) p volume ^ 2 ≤
        D * glyzDyadicBlock
          (fun j => lpNorm ((glyzDyadicBlock f N m j : SchwartzMap (GlyzSpace l) ℂ) : GlyzSpace l → ℂ) p volume ^ 2) m n i := by
  obtain ⟨ρ, R, hρ, hρ1, hR, hstep⟩ :=
    exists_uniform_glyzCoordinateCurve_decoupling_step l r hν
  refine ⟨ρ, R, hρ, hρ1, hR, fun t a b ha hb hab hshort hsep δ hδ hδκ hscale
    N n m i hnm hmN s f p D hs hf hD => ?_⟩
  have h := hstep t a b ha hb hab hshort hsep δ hδ hδκ hscale
    (Finset.range (2 ^ (m - n))) s
    (fun j => glyzDyadicBlock f N m (i * 2 ^ (m - n) + j)) p D
    (fun j hj => hs j (Finset.mem_range.mp hj)) (fun j hj => hf j (Finset.mem_range.mp hj))
    (fun g hg => hD g (fun j hj => hg j (Finset.mem_range.mpr hj)))
  have he := glyzDyadicBlock_comp f N n m i hnm hmN
  change (∑ j ∈ Finset.range (2 ^ (m - n)), glyzDyadicBlock f N m (i * 2 ^ (m - n) + j)) =
    glyzDyadicBlock f N n i at he
  rw [he] at h
  exact h

/-- The parent estimate also allows arbitrary fixed enlargement of all
grouped child supports. A parent of actual finest pieces satisfies the Taylor
one-step estimate as soon as its grouped children have the certified
curve-box supports. The only analytic assumption is the enlarged
moment-box estimate for those child centers. -/
theorem exists_uniform_glyzCoordinateCurve_enlarged_block_step
    (l r : ℕ) {ν Q : ℝ} (hν : 0 < ν) (hQ : 0 < Q) :
    ∃ ρ R : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 0 < R ∧
      ∀ (t a b : ℝ), a ∈ Set.Icc (-1 : ℝ) 1 → b ∈ Set.Icc (-1 : ℝ) 1 →
      a < b → b - a < ρ → (a, t) ∈ separatedMixedCenters ν →
      ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ b - a → (b - a) ^ (l + 1) ≤ δ ^ l →
      ∀ (N n m i : ℕ), n ≤ m → m ≤ N →
      ∀ (s : ℕ → ℝ) (f : ℕ → SchwartzMap (GlyzSpace l) ℂ) (p : ℝ≥0∞) (D : ℝ),
      (∀ j < 2 ^ (m - n), s j ∈ Set.Icc a b ∧ (s j, t) ∈ separatedMixedCenters ν) →
      (∀ j < 2 ^ (m - n), Function.support (𝓕
        ((glyzDyadicBlock f N m (i * 2 ^ (m - n) + j) : SchwartzMap (GlyzSpace l) ℂ) : GlyzSpace l → ℂ)) ⊆
          glyzEnlargedCurveBox (glyzCoordinateCurve l r t) l (s j) δ Q) →
      (∀ g : ℕ → SchwartzMap (GlyzSpace l) ℂ,
        (∀ j < 2 ^ (m - n), Function.support (𝓕 (g j : GlyzSpace l → ℂ)) ⊆
          glyzFrequencyBox (glyzMomentFrequencyFrame l (s j - a) δ hδ)
            ((EuclideanSpace.equiv (Fin l) ℝ).symm (glyzMomentCurve l (s j - a))) R) →
        lpNorm ((∑ j ∈ Finset.range (2 ^ (m - n)), g j : SchwartzMap (GlyzSpace l) ℂ) :
          GlyzSpace l → ℂ) p volume ^ 2 ≤
          D * ∑ j ∈ Finset.range (2 ^ (m - n)), lpNorm (g j : GlyzSpace l → ℂ) p volume ^ 2) →
      lpNorm ((glyzDyadicBlock f N n i : SchwartzMap (GlyzSpace l) ℂ) : GlyzSpace l → ℂ) p volume ^ 2 ≤
        D * glyzDyadicBlock
          (fun j => lpNorm ((glyzDyadicBlock f N m j : SchwartzMap (GlyzSpace l) ℂ) : GlyzSpace l → ℂ) p volume ^ 2) m n i := by
  obtain ⟨ρ, R, hρ, hρ1, hR, hstep⟩ :=
    exists_uniform_glyzCoordinateCurve_enlarged_decoupling_step l r hν hQ
  refine ⟨ρ, R, hρ, hρ1, hR, fun t a b ha hb hab hshort hsep δ hδ hδκ hscale
    N n m i hnm hmN s f p D hs hf hD => ?_⟩
  have h := hstep t a b ha hb hab hshort hsep δ hδ hδκ hscale
    (Finset.range (2 ^ (m - n))) s
    (fun j => glyzDyadicBlock f N m (i * 2 ^ (m - n) + j)) p D
    (fun j hj => hs j (Finset.mem_range.mp hj)) (fun j hj => hf j (Finset.mem_range.mp hj))
    (fun g hg => hD g (fun j hj => hg j (Finset.mem_range.mpr hj)))
  have he := glyzDyadicBlock_comp f N n m i hnm hmN
  change (∑ j ∈ Finset.range (2 ^ (m - n)), glyzDyadicBlock f N m (i * 2 ^ (m - n) + j)) =
    glyzDyadicBlock f N n i at he
  rw [he] at h
  exact h


end PlanarNikodym
