import PlanarNikodym.Analysis.Fourier.GlyzDecouplingConstants
import PlanarNikodym.Analysis.Fourier.GlyzDyadicRescaling
import PlanarNikodym.Analysis.Fourier.GlyzBilinearNormBounds

/-! Optimal constants for actual separated dyadic convolution-power
bilinear integrals. These are the `p`-th powers of the usual asymmetric
constants, so no root or infinite ENNReal value is hidden in the
optimization. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace PlanarNikodym

def glyzDyadicDepth (N : ℕ) (a : ℝ) : ℕ := ⌈a * N⌉₊

theorem glyzDyadicDepth_le {N : ℕ} {a : ℝ} (ha : a ≤ 1) :
    glyzDyadicDepth N a ≤ N := by
  rw [glyzDyadicDepth, Nat.ceil_le]
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- Distance at least one quarter between the actual two parent
intervals, expressed by their centers and lengths. -/
def GlyzDyadicSeparated (n n' i j : ℕ) : Prop :=
  1 / 4 + (glyzDyadicScale n + glyzDyadicScale n') / 2 ≤
    |glyzDyadicCenter n i - glyzDyadicCenter n' j|

def glyzDyadicPolarMeasure (m A n i : ℕ) : Measure (GlyzSpace m) :=
  glyzPolarMeasure A (glyzMomentFrequencyFrame m (glyzDyadicCenter n i)
    (glyzDyadicScale n) (glyzDyadicScale_pos n))

def glyzDyadicBilinearValue (m A N n n' : ℕ) (p : ℝ≥0) (a : ℝ)
    (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) (i j : ℕ) : ℝ :=
  (glyzWeightedBilinear (glyzDyadicPolarMeasure m A n i)
    (glyzDyadicPolarMeasure m A n' j)
    (glyzDyadicBlock f N n i : SchwartzMap (GlyzSpace m) ℂ)
    (glyzDyadicBlock f N n' j : SchwartzMap (GlyzSpace m) ℂ) a ((p : ℝ) - a)).toReal

def glyzDyadicBilinearEnergy (m N n n' : ℕ) (p : ℝ≥0) (a : ℝ)
    (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) (i j : ℕ) : ℝ :=
  (glyzDyadicBlock (fun k => lpNorm (f k) p volume ^ (2 : ℕ)) N n i) ^ (a / 2) *
    (glyzDyadicBlock (fun k => lpNorm (f k) p volume ^ (2 : ℕ)) N n' j) ^
      (((p : ℝ) - a) / 2)

theorem glyz_dyadic_square_block_nonneg (m N n i : ℕ) (p : ℝ≥0)
    (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) :
    0 ≤ glyzDyadicBlock (fun k => lpNorm (f k) p volume ^ (2 : ℕ)) N n i :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem glyzDyadicBilinearEnergy_nonneg (m N n n' : ℕ) (p : ℝ≥0) (a : ℝ)
    (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) (i j : ℕ) :
    0 ≤ glyzDyadicBilinearEnergy m N n n' p a f i j := by
  unfold glyzDyadicBilinearEnergy
  exact mul_nonneg
    (Real.rpow_nonneg (glyz_dyadic_square_block_nonneg m N n i p f) _)
    (Real.rpow_nonneg (glyz_dyadic_square_block_nonneg m N n' j p f) _)

theorem glyz_schwartz_block_square_le_trivial (m N n i : ℕ) (p : ℝ≥0) (hp : 1 ≤ p)
    (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) :
    lpNorm (⇑(glyzDyadicBlock f N n i)) p volume ^ (2 : ℕ) ≤
      (2 : ℝ) ^ N * glyzDyadicBlock (fun k => lpNorm (f k) p volume ^ (2 : ℕ)) N n i := by
  have h := glyz_schwartz_dyadic_square_le_trivial m (N - n) p hp
    (fun k => f (i * 2 ^ (N - n) + k))
  have he : ((glyzDyadicBlock f N n i : SchwartzMap (GlyzSpace m) ℂ) :
      GlyzSpace m → ℂ) =
      fun x => ∑ k ∈ Finset.range (2 ^ (N - n)), f (i * 2 ^ (N - n) + k) x := by
    ext x
    simp [glyzDyadicBlock]
  rw [he]
  exact h.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le N n))
    (glyz_dyadic_square_block_nonneg m N n i p f))

def GlyzAsymmetricIntegralBound (m A N n n' : ℕ) (p : ℝ≥0) (a C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ f : ℕ → SchwartzMap (GlyzSpace m) ℂ,
    GlyzDyadicSupported m N f →
    ∀ i < 2 ^ n, ∀ j < 2 ^ n', GlyzDyadicSeparated n n' i j →
      glyzDyadicBilinearValue m A N n n' p a f i j ≤
        C * glyzDyadicBilinearEnergy m N n n' p a f i j

def glyzAsymmetricIntegralConstant (m A N n n' : ℕ) (p : ℝ≥0) (a : ℝ) : ℝ :=
  sInf {C : ℝ | GlyzAsymmetricIntegralBound m A N n n' p a C}

theorem glyz_asymmetric_integral_bound_trivial {m A : ℕ} (hA : m < A)
    (N n n' : ℕ) (p : ℝ≥0) (hp : 1 ≤ p) {a : ℝ}
    (ha : 0 ≤ a) (hap : a ≤ (p : ℝ)) :
    GlyzAsymmetricIntegralBound m A N n n' p a
      (glyzPolarMass m A ^ (2 : ℕ) * ((2 : ℝ) ^ N) ^ ((p : ℝ) / 2)) := by
  refine ⟨mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) _),
    fun f _ i _ j _ _ => ?_⟩
  have h := glyz_polar_bilinear_toReal_le_sq_lpNorm_bounds hA
    (glyzMomentFrequencyFrame m (glyzDyadicCenter n i) (glyzDyadicScale n)
      (glyzDyadicScale_pos n))
    (glyzMomentFrequencyFrame m (glyzDyadicCenter n' j) (glyzDyadicScale n')
      (glyzDyadicScale_pos n'))
    (glyzDyadicBlock f N n i) (glyzDyadicBlock f N n' j)
    (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hp) ha hap
    (glyz_schwartz_block_square_le_trivial m N n i p hp f)
    (glyz_schwartz_block_square_le_trivial m N n' j p hp f)
  apply h.trans_eq
  rw [Real.mul_rpow (by positivity) (glyz_dyadic_square_block_nonneg m N n i p f),
    Real.mul_rpow (by positivity) (glyz_dyadic_square_block_nonneg m N n' j p f)]
  have hpow : ((2 : ℝ) ^ N) ^ (a / 2) * ((2 : ℝ) ^ N) ^ (((p : ℝ) - a) / 2) =
      ((2 : ℝ) ^ N) ^ ((p : ℝ) / 2) := by
    rw [← Real.rpow_add (by positivity)]
    congr 1
    ring
  dsimp only [glyzDyadicBilinearEnergy]
  calc
    _ = glyzPolarMass m A ^ (2 : ℕ) *
        (((2 : ℝ) ^ N) ^ (a / 2) * ((2 : ℝ) ^ N) ^ (((p : ℝ) - a) / 2)) *
        ((glyzDyadicBlock (fun k => lpNorm (f k) p volume ^ (2 : ℕ)) N n i) ^ (a / 2) *
        (glyzDyadicBlock (fun k => lpNorm (f k) p volume ^ (2 : ℕ)) N n' j) ^
          (((p : ℝ) - a) / 2)) := by ring
    _ = _ := by rw [hpow]

theorem glyz_asymmetric_integral_bounds_nonempty {m A : ℕ} (hA : m < A)
    (N n n' : ℕ) (p : ℝ≥0) (hp : 1 ≤ p) {a : ℝ}
    (ha : 0 ≤ a) (hap : a ≤ (p : ℝ)) :
    {C : ℝ | GlyzAsymmetricIntegralBound m A N n n' p a C}.Nonempty :=
  ⟨_, glyz_asymmetric_integral_bound_trivial hA N n n' p hp ha hap⟩

theorem glyz_asymmetric_integral_bounds_bddBelow
    (m A N n n' : ℕ) (p : ℝ≥0) (a : ℝ) :
    BddBelow {C : ℝ | GlyzAsymmetricIntegralBound m A N n n' p a C} :=
  ⟨0, fun _ hC => hC.1⟩

theorem glyzAsymmetricIntegralConstant_nonneg {m A : ℕ} (hA : m < A)
    (N n n' : ℕ) (p : ℝ≥0) (hp : 1 ≤ p) {a : ℝ}
    (ha : 0 ≤ a) (hap : a ≤ (p : ℝ)) :
    0 ≤ glyzAsymmetricIntegralConstant m A N n n' p a :=
  le_csInf (glyz_asymmetric_integral_bounds_nonempty hA N n n' p hp ha hap)
    fun _ hC => hC.1

theorem glyzAsymmetricIntegralConstant_le {m A N n n' : ℕ} {p : ℝ≥0} {a C : ℝ}
    (hC : GlyzAsymmetricIntegralBound m A N n n' p a C) :
    glyzAsymmetricIntegralConstant m A N n n' p a ≤ C :=
  csInf_le (glyz_asymmetric_integral_bounds_bddBelow m A N n n' p a) hC

theorem glyzAsymmetricIntegralConstant_bound {m A : ℕ} (hA : m < A)
    (N n n' : ℕ) (p : ℝ≥0) (hp : 1 ≤ p) {a : ℝ}
    (ha : 0 ≤ a) (hap : a ≤ (p : ℝ)) :
    GlyzAsymmetricIntegralBound m A N n n' p a
      (glyzAsymmetricIntegralConstant m A N n n' p a) := by
  refine ⟨glyzAsymmetricIntegralConstant_nonneg hA N n n' p hp ha hap,
    fun f hf i hi j hj hs => ?_⟩
  have hE := glyzDyadicBilinearEnergy_nonneg m N n n' p a f i j
  rcases eq_or_lt_of_le hE with hE0 | hEpos
  · have h := (glyz_asymmetric_integral_bound_trivial hA N n n' p hp ha hap).2
      f hf i hi j hj hs
    simpa only [← hE0, mul_zero] using h
  · have hratio : glyzDyadicBilinearValue m A N n n' p a f i j /
        glyzDyadicBilinearEnergy m N n n' p a f i j ≤
        glyzAsymmetricIntegralConstant m A N n n' p a :=
      le_csInf (glyz_asymmetric_integral_bounds_nonempty hA N n n' p hp ha hap)
        (fun C hC => (div_le_iff₀ hEpos).mpr (hC.2 f hf i hi j hj hs))
    exact (div_le_iff₀ hEpos).mp hratio

/-- The optimized real constant also bounds the original nonnegative
integral. The proof verifies finiteness before undoing `toReal`. -/
theorem glyzAsymmetricIntegralConstant_ennreal_bound {m A : ℕ} (hA : m < A)
    (N n n' : ℕ) (p : ℝ≥0) (hp : 1 ≤ p) {a : ℝ}
    (ha : 0 ≤ a) (hap : a ≤ (p : ℝ))
    (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) (hf : GlyzDyadicSupported m N f)
    {i j : ℕ} (hi : i < 2 ^ n) (hj : j < 2 ^ n') (hs : GlyzDyadicSeparated n n' i j) :
    glyzWeightedBilinear (glyzDyadicPolarMeasure m A n i)
      (glyzDyadicPolarMeasure m A n' j)
      (glyzDyadicBlock f N n i : SchwartzMap (GlyzSpace m) ℂ)
      (glyzDyadicBlock f N n' j : SchwartzMap (GlyzSpace m) ℂ) a ((p : ℝ) - a) ≤
      ENNReal.ofReal (glyzAsymmetricIntegralConstant m A N n n' p a *
        glyzDyadicBilinearEnergy m N n n' p a f i j) := by
  have hfinite := glyz_polar_bilinear_lt_top hA
    (glyzMomentFrequencyFrame m (glyzDyadicCenter n i) (glyzDyadicScale n)
      (glyzDyadicScale_pos n))
    (glyzMomentFrequencyFrame m (glyzDyadicCenter n' j) (glyzDyadicScale n')
      (glyzDyadicScale_pos n'))
    (glyzDyadicBlock f N n i) (glyzDyadicBlock f N n' j)
    (show (0 : ℝ) < p by exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hp)
    ha hap
  have h := ENNReal.ofReal_le_ofReal
    ((glyzAsymmetricIntegralConstant_bound hA N n n' p hp ha hap).2 f hf i hi j hj hs)
  have hfinite' : glyzWeightedBilinear (glyzDyadicPolarMeasure m A n i)
      (glyzDyadicPolarMeasure m A n' j)
      (glyzDyadicBlock f N n i : SchwartzMap (GlyzSpace m) ℂ)
      (glyzDyadicBlock f N n' j : SchwartzMap (GlyzSpace m) ℂ) a ((p : ℝ) - a) ≠ ⊤ :=
    hfinite.ne
  simpa only [glyzDyadicBilinearValue, ENNReal.ofReal_toReal hfinite'] using h

/-- Actual scale-dependent bilinear exponents. The two parent depths
are the dyadic roundings of `alpha * N` and `beta * N`. -/
def GlyzAdmissibleAsymmetricLoss (m A : ℕ) (p : ℝ≥0) (a alpha beta e : ℝ) : Prop :=
  0 ≤ e ∧ ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
    glyzAsymmetricIntegralConstant m A N (glyzDyadicDepth N alpha)
      (glyzDyadicDepth N beta) p a ≤ C * (2 : ℝ) ^ (e * N)

theorem glyz_admissible_asymmetric_loss_trivial {m A : ℕ} (hA : m < A)
    (p : ℝ≥0) (hp : 1 ≤ p) {a : ℝ} (ha : 0 ≤ a) (hap : a ≤ (p : ℝ))
    (alpha beta : ℝ) :
    GlyzAdmissibleAsymmetricLoss m A p a alpha beta ((p : ℝ) / 2) := by
  refine ⟨by positivity, glyzPolarMass m A ^ (2 : ℕ),
    sq_pos_of_pos (glyzPolarMass_pos hA), fun N => ?_⟩
  have h := glyzAsymmetricIntegralConstant_le
    (glyz_asymmetric_integral_bound_trivial hA N
      (glyzDyadicDepth N alpha) (glyzDyadicDepth N beta) p hp ha hap)
  convert h using 1
  rw [← Real.rpow_natCast (2 : ℝ) N, ← Real.rpow_mul (by norm_num)]
  congr 2
  ring

theorem glyz_admissible_asymmetric_loss_mono {m A : ℕ} {p : ℝ≥0}
    {a alpha beta e e' : ℝ}
    (he : GlyzAdmissibleAsymmetricLoss m A p a alpha beta e) (hee : e ≤ e') :
    GlyzAdmissibleAsymmetricLoss m A p a alpha beta e' := by
  obtain ⟨he, C, hC, h⟩ := he
  refine ⟨he.trans hee, C, hC, fun N => (h N).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right hee (Nat.cast_nonneg N))) hC.le

def glyzOptimalAsymmetricLoss (m A : ℕ) (p : ℝ≥0) (a alpha beta : ℝ) : ℝ :=
  sInf {e : ℝ | GlyzAdmissibleAsymmetricLoss m A p a alpha beta e}

theorem glyzOptimalAsymmetricLoss_nonneg {m A : ℕ} (hA : m < A)
    (p : ℝ≥0) (hp : 1 ≤ p) {a : ℝ} (ha : 0 ≤ a) (hap : a ≤ (p : ℝ))
    (alpha beta : ℝ) :
    0 ≤ glyzOptimalAsymmetricLoss m A p a alpha beta :=
  le_csInf ⟨_, glyz_admissible_asymmetric_loss_trivial hA p hp ha hap alpha beta⟩
    fun _ he => he.1

theorem glyzOptimalAsymmetricLoss_le {m A : ℕ} {p : ℝ≥0} {a alpha beta e : ℝ}
    (he : GlyzAdmissibleAsymmetricLoss m A p a alpha beta e) :
    glyzOptimalAsymmetricLoss m A p a alpha beta ≤ e :=
  csInf_le ⟨0, fun _ he => he.1⟩ he

theorem glyzOptimalAsymmetricLoss_le_trivial {m A : ℕ} (hA : m < A)
    (p : ℝ≥0) (hp : 1 ≤ p) {a : ℝ} (ha : 0 ≤ a) (hap : a ≤ (p : ℝ))
    (alpha beta : ℝ) :
    glyzOptimalAsymmetricLoss m A p a alpha beta ≤ (p : ℝ) / 2 :=
  glyzOptimalAsymmetricLoss_le
    (glyz_admissible_asymmetric_loss_trivial hA p hp ha hap alpha beta)

theorem glyz_admissible_asymmetric_loss_of_optimal_lt {m A : ℕ} (hA : m < A)
    (p : ℝ≥0) (hp : 1 ≤ p) {a : ℝ} (ha : 0 ≤ a) (hap : a ≤ (p : ℝ))
    (alpha beta : ℝ) {e : ℝ} (he : glyzOptimalAsymmetricLoss m A p a alpha beta < e) :
    GlyzAdmissibleAsymmetricLoss m A p a alpha beta e := by
  obtain ⟨b, hb, hbe⟩ := exists_lt_of_csInf_lt
    (s := {e : ℝ | GlyzAdmissibleAsymmetricLoss m A p a alpha beta e})
    ⟨_, glyz_admissible_asymmetric_loss_trivial hA p hp ha hap alpha beta⟩ he
  exact glyz_admissible_asymmetric_loss_mono hb hbe.le

theorem glyz_asymmetric_integral_of_admissible_loss {m A : ℕ} (hA : m < A)
    (p : ℝ≥0) (hp : 1 ≤ p) {a : ℝ} (ha : 0 ≤ a) (hap : a ≤ (p : ℝ))
    {alpha beta e : ℝ} (he : GlyzAdmissibleAsymmetricLoss m A p a alpha beta e) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ f : ℕ → SchwartzMap (GlyzSpace m) ℂ,
      GlyzDyadicSupported m N f →
      ∀ i < 2 ^ glyzDyadicDepth N alpha, ∀ j < 2 ^ glyzDyadicDepth N beta,
      GlyzDyadicSeparated (glyzDyadicDepth N alpha) (glyzDyadicDepth N beta) i j →
        glyzDyadicBilinearValue m A N (glyzDyadicDepth N alpha)
          (glyzDyadicDepth N beta) p a f i j ≤
          C * (2 : ℝ) ^ (e * N) *
            glyzDyadicBilinearEnergy m N (glyzDyadicDepth N alpha)
              (glyzDyadicDepth N beta) p a f i j := by
  obtain ⟨_, C, hC, h⟩ := he
  refine ⟨C, hC, fun N f hf i hi j hj hs => ?_⟩
  exact ((glyzAsymmetricIntegralConstant_bound hA N
    (glyzDyadicDepth N alpha) (glyzDyadicDepth N beta) p hp ha hap).2 f hf i hi j hj hs).trans
    (mul_le_mul_of_nonneg_right (h N)
      (glyzDyadicBilinearEnergy_nonneg m N _ _ p a f i j))

end PlanarNikodym
