import PlanarNikodym.Analysis.Fourier.GlyzBilinearCoarseSum
import PlanarNikodym.Analysis.Fourier.GlyzDyadicBlockSupport

/-! The actual coarse unweighted integral is controlled by the optimal
fine asymmetric constant. This is the main comparison in GLYZ Lemma
3.4, with its dyadic cardinality loss written explicitly. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace PlanarNikodym

/-- The constant is chosen before all depths, all separated coarse
parents, and all Fourier-supported Schwartz families. Both fine
families are the actual subdivisions of those same coarse blocks. -/
theorem exists_glyz_asymmetric_reverse_comparison {m A : ℕ} (hA : m < A)
    (p : ℝ≥0) {a : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ (p : ℝ) - a) :
    ∃ K : ℝ, 0 < K ∧ ∀ N n q q' : ℕ, n + q ≤ N → n + q' ≤ N →
      ∀ i < 2 ^ n, ∀ j < 2 ^ n, GlyzDyadicSeparated n n i j →
      ∀ f : ℕ → SchwartzMap (GlyzSpace m) ℂ, GlyzDyadicSupported m N f →
      glyzBareBilinear (glyzDyadicBlock f N n i : SchwartzMap (GlyzSpace m) ℂ)
        (glyzDyadicBlock f N n j : SchwartzMap (GlyzSpace m) ℂ) a ((p : ℝ) - a) ≤
        ENNReal.ofReal K * (2 ^ q : ℝ≥0∞) ^ a * (2 ^ q' : ℝ≥0∞) ^ ((p : ℝ) - a) *
          ENNReal.ofReal (glyzAsymmetricIntegralConstant m A N (n + q) (n + q') p a) *
          ENNReal.ofReal (glyzDyadicBilinearEnergy m N n n p a f i j) := by
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have hb0 : 0 ≤ (p : ℝ) - a := zero_le_one.trans hb
  have hap : a ≤ (p : ℝ) := sub_nonneg.mp hb0
  have hp : 1 ≤ p := by
    have hp' : (1 : ℝ) ≤ p := by linarith
    exact_mod_cast hp'
  obtain ⟨K₁, hK₁, hunc₁⟩ := glyz_dyadic_block_uncertainty m A
    (p := ⟨a, ha0⟩) (show (1 : ℝ≥0) ≤ ⟨a, ha0⟩ from ha)
  obtain ⟨K₂, hK₂, hunc₂⟩ := glyz_dyadic_block_uncertainty m A
    (p := ⟨(p : ℝ) - a, hb0⟩) (show (1 : ℝ≥0) ≤ ⟨(p : ℝ) - a, hb0⟩ from hb)
  refine ⟨K₁ * K₂, mul_pos hK₁ hK₂, fun N n q q' hq hq' i hi j hj hs f hf => ?_⟩
  let F : ℕ → SchwartzMap (GlyzSpace m) ℂ :=
    fun u => glyzDyadicBlock f N (n + q) (i * 2 ^ q + u)
  let G : ℕ → SchwartzMap (GlyzSpace m) ℂ :=
    fun v => glyzDyadicBlock f N (n + q') (j * 2 ^ q' + v)
  let B := glyzAsymmetricIntegralConstant m A N (n + q) (n + q') p a
  let W : ℕ → ℝ := fun k => lpNorm (f k) p volume ^ (2 : ℕ)
  let E := glyzDyadicBilinearEnergy m N n n p a f i j
  have hB : 0 ≤ B := glyzAsymmetricIntegralConstant_nonneg hA N _ _ p hp ha0 hap
  have hE : 0 ≤ E := glyzDyadicBilinearEnergy_nonneg m N n n p a f i j
  have hpair (u : ℕ) (hu : u ∈ Finset.range (2 ^ q))
      (v : ℕ) (hv : v ∈ Finset.range (2 ^ q')) :
      glyzBareBilinear (F u) (G v) a ((p : ℝ) - a) ≤
        (ENNReal.ofReal K₁ * ENNReal.ofReal K₂) * ENNReal.ofReal (B * E) := by
    have hui := glyz_dyadic_descendant_lt hi (Finset.mem_range.mp hu)
    have hvj := glyz_dyadic_descendant_lt hj (Finset.mem_range.mp hv)
    let μ := glyzDyadicPolarMeasure m A (n + q) (i * 2 ^ q + u)
    let ν := glyzDyadicPolarMeasure m A (n + q') (j * 2 ^ q' + v)
    letI : IsFiniteMeasure μ := isFiniteMeasure_glyzPolarMeasure hA _
    letI : IsFiniteMeasure ν := isFiniteMeasure_glyzPolarMeasure hA _
    have hunc := glyzBareBilinear_le_weighted μ ν (F u) (G v) a ((p : ℝ) - a)
      (ENNReal.ofReal K₁) (ENNReal.ofReal K₂) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
      (hunc₁ N (n + q) (i * 2 ^ q + u) hq hui f hf)
      (hunc₂ N (n + q') (j * 2 ^ q' + v) hq' hvj f hf)
    have hbil := glyzAsymmetricIntegralConstant_ennreal_bound hA N (n + q) (n + q')
      p hp ha0 hap f hf hui hvj
      (glyzDyadicSeparated_descendants hs (Finset.mem_range.mp hu) (Finset.mem_range.mp hv))
    have hW (k : ℕ) : 0 ≤ W k := sq_nonneg _
    have huE : glyzDyadicBlock W N (n + q) (i * 2 ^ q + u) ≤ glyzDyadicBlock W N n i := by
      simpa only [Nat.add_sub_cancel_left] using
        glyzDyadicBlock_descendant_le W hW N (n + q) n i u (by omega) hq
          (by simpa only [Nat.add_sub_cancel_left] using Finset.mem_range.mp hu)
    have hvE : glyzDyadicBlock W N (n + q') (j * 2 ^ q' + v) ≤ glyzDyadicBlock W N n j := by
      simpa only [Nat.add_sub_cancel_left] using
        glyzDyadicBlock_descendant_le W hW N (n + q') n j v (by omega) hq'
          (by simpa only [Nat.add_sub_cancel_left] using Finset.mem_range.mp hv)
    have henergy : glyzDyadicBilinearEnergy m N (n + q) (n + q') p a f
        (i * 2 ^ q + u) (j * 2 ^ q' + v) ≤ E :=
      mul_le_mul
        (Real.rpow_le_rpow (glyz_dyadic_square_block_nonneg m N _ _ p f) huE (by positivity))
        (Real.rpow_le_rpow (glyz_dyadic_square_block_nonneg m N _ _ p f) hvE (by positivity))
        (Real.rpow_nonneg (glyz_dyadic_square_block_nonneg m N _ _ p f) _)
        (Real.rpow_nonneg (glyz_dyadic_square_block_nonneg m N _ _ p f) _)
    apply hunc.trans
    apply mul_le_mul_right
    exact hbil.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left henergy hB))
  have hsum := glyzBareBilinear_sum_le_uniform (Finset.range (2 ^ q))
    (Finset.range (2 ^ q')) F G ha hb hpair
  have hF : (fun x => ∑ u ∈ Finset.range (2 ^ q), F u x) =
      (glyzDyadicBlock f N n i : SchwartzMap (GlyzSpace m) ℂ) := by
    ext x
    have h := congrArg (fun f : SchwartzMap (GlyzSpace m) ℂ => f x)
      (glyzDyadicBlock_refine f N n q i hq)
    simpa only [F, sum_apply] using h.symm
  have hG : (fun x => ∑ v ∈ Finset.range (2 ^ q'), G v x) =
      (glyzDyadicBlock f N n j : SchwartzMap (GlyzSpace m) ℂ) := by
    ext x
    have h := congrArg (fun f : SchwartzMap (GlyzSpace m) ℂ => f x)
      (glyzDyadicBlock_refine f N n q' j hq')
    simpa only [G, sum_apply] using h.symm
  rw [hF, hG, Finset.card_range, Finset.card_range] at hsum
  apply hsum.trans_eq
  rw [ENNReal.ofReal_mul hB, ENNReal.ofReal_mul hK₁.le]
  dsimp only [B, E]
  push_cast
  ring

end PlanarNikodym
