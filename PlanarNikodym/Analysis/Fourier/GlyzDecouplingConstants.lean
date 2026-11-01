import PlanarNikodym.Analysis.Fourier.GlyzMomentBoxes
import PlanarNikodym.Analysis.Fourier.GlyzBilinearReduction
import Mathlib.Algebra.Order.Chebyshev

/-! Actual dyadic moment-curve decoupling constants and their optimal
growth exponent. We use the square of the usual constant, so that the
elementary bound is `2 ^ N` and a loss `a` here is a loss `a / 2` in the
unsquared norm inequality. Every constant quantifies over actual Schwartz
families with the prescribed Fourier supports. -/
noncomputable section
open Set MeasureTheory FourierTransform
open scoped BigOperators NNReal ENNReal FourierTransform
namespace PlanarNikodym

/-- The actual frequency support condition for the `2 ^ N` dyadic moment
pieces. The dyadic centers and lengths are written explicitly to keep the
constant independent of the affine-rescaling implementation. -/
def GlyzDyadicSupported (m N : ℕ) (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) : Prop :=
  ∀ i ∈ Finset.range (2 ^ N),
    Function.support (𝓕 (f i : GlyzSpace m → ℂ)) ⊆
      glyzMomentFrequencyBox m (((2 : ℝ) ^ N)⁻¹ * ((i : ℝ) + 1 / 2))
        (((2 : ℝ) ^ N)⁻¹) (by positivity)

def glyzDyadicSquareEnergy (m N : ℕ) (p : ℝ≥0)
    (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) : ℝ :=
  ∑ i ∈ Finset.range (2 ^ N), lpNorm (f i) p volume ^ (2 : ℕ)

theorem glyzDyadicSquareEnergy_nonneg (m N : ℕ) (p : ℝ≥0)
    (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) :
    0 ≤ glyzDyadicSquareEnergy m N p f :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Admissible squared constants, with all analytic test functions
universally quantified. -/
def GlyzDyadicSquareBound (m N : ℕ) (p : ℝ≥0) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ f : ℕ → SchwartzMap (GlyzSpace m) ℂ,
    GlyzDyadicSupported m N f →
    lpNorm (fun x => ∑ i ∈ Finset.range (2 ^ N), f i x) p volume ^ (2 : ℕ) ≤
      C * glyzDyadicSquareEnergy m N p f

theorem glyz_schwartz_dyadic_square_le_trivial (m N : ℕ) (p : ℝ≥0) (hp : 1 ≤ p)
    (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) :
    lpNorm (fun x => ∑ i ∈ Finset.range (2 ^ N), f i x) p volume ^ (2 : ℕ) ≤
      (2 : ℝ) ^ N * glyzDyadicSquareEnergy m N p f := by
  have hsum : lpNorm (fun x => ∑ i ∈ Finset.range (2 ^ N), f i x) p volume ≤
      ∑ i ∈ Finset.range (2 ^ N), lpNorm (f i) p volume := by
    have h := lpNorm_sum_le (s := Finset.range (2 ^ N))
      (fun i _ => (f i).memLp p volume)
      (show (1 : ℝ≥0∞) ≤ (p : ℝ≥0∞) by exact_mod_cast hp)
    convert h using 1
    congr 1
    ext x
    simp only [Finset.sum_apply]
  calc
    _ ≤ (∑ i ∈ Finset.range (2 ^ N), lpNorm (f i) p volume) ^ (2 : ℕ) :=
      pow_le_pow_left₀ lpNorm_nonneg hsum 2
    _ ≤ ((Finset.range (2 ^ N)).card : ℝ) *
        ∑ i ∈ Finset.range (2 ^ N), lpNorm (f i) p volume ^ (2 : ℕ) :=
      sq_sum_le_card_mul_sum_sq
    _ = _ := by simp [glyzDyadicSquareEnergy]

theorem glyz_dyadic_square_bound_trivial (m N : ℕ) (p : ℝ≥0) (hp : 1 ≤ p) :
    GlyzDyadicSquareBound m N p ((2 : ℝ) ^ N) :=
  ⟨by positivity, fun f _ => glyz_schwartz_dyadic_square_le_trivial m N p hp f⟩

theorem glyz_dyadic_square_bound_mono {m N : ℕ} {p : ℝ≥0} {C D : ℝ}
    (hC : GlyzDyadicSquareBound m N p C) (hCD : C ≤ D) :
    GlyzDyadicSquareBound m N p D :=
  ⟨hC.1.trans hCD, fun f hf => (hC.2 f hf).trans
    (mul_le_mul_of_nonneg_right hCD (glyzDyadicSquareEnergy_nonneg m N p f))⟩

def glyzDyadicSquareConstant (m N : ℕ) (p : ℝ≥0) : ℝ :=
  sInf {C : ℝ | GlyzDyadicSquareBound m N p C}

theorem glyz_dyadic_square_bounds_nonempty (m N : ℕ) (p : ℝ≥0) (hp : 1 ≤ p) :
    {C : ℝ | GlyzDyadicSquareBound m N p C}.Nonempty :=
  ⟨_, glyz_dyadic_square_bound_trivial m N p hp⟩

theorem glyz_dyadic_square_bounds_bddBelow (m N : ℕ) (p : ℝ≥0) :
    BddBelow {C : ℝ | GlyzDyadicSquareBound m N p C} :=
  ⟨0, fun _ hC => hC.1⟩

theorem glyzDyadicSquareConstant_nonneg (m N : ℕ) (p : ℝ≥0) (hp : 1 ≤ p) :
    0 ≤ glyzDyadicSquareConstant m N p :=
  le_csInf (glyz_dyadic_square_bounds_nonempty m N p hp) fun _ hC => hC.1

theorem glyzDyadicSquareConstant_le {m N : ℕ} {p : ℝ≥0} {C : ℝ}
    (hC : GlyzDyadicSquareBound m N p C) :
    glyzDyadicSquareConstant m N p ≤ C :=
  csInf_le (glyz_dyadic_square_bounds_bddBelow m N p) hC

theorem glyzDyadicSquareConstant_le_trivial (m N : ℕ) (p : ℝ≥0) (hp : 1 ≤ p) :
    glyzDyadicSquareConstant m N p ≤ (2 : ℝ) ^ N :=
  glyzDyadicSquareConstant_le (glyz_dyadic_square_bound_trivial m N p hp)

/-- The infimum is itself a valid constant. In particular the definition
does not silently lose the norm inequality at the optimal value. -/
theorem glyzDyadicSquareConstant_bound (m N : ℕ) (p : ℝ≥0) (hp : 1 ≤ p) :
    GlyzDyadicSquareBound m N p (glyzDyadicSquareConstant m N p) := by
  refine ⟨glyzDyadicSquareConstant_nonneg m N p hp, fun f hf => ?_⟩
  have hE := glyzDyadicSquareEnergy_nonneg m N p f
  rcases eq_or_lt_of_le hE with hE0 | hEpos
  · have h := (glyz_dyadic_square_bound_trivial m N p hp).2 f hf
    simpa only [← hE0, mul_zero] using h
  · have hratio : lpNorm (fun x => ∑ i ∈ Finset.range (2 ^ N), f i x) p volume ^
        (2 : ℕ) / glyzDyadicSquareEnergy m N p f ≤ glyzDyadicSquareConstant m N p :=
      le_csInf (glyz_dyadic_square_bounds_nonempty m N p hp)
        (fun C hC => (div_le_iff₀ hEpos).mpr (hC.2 f hf))
    exact (div_le_iff₀ hEpos).mp hratio

/-- Uniform exponential growth bounds on the actual optimal constants.
The coefficient is chosen once, before the dyadic depth. -/
def GlyzAdmissibleSquareLoss (m : ℕ) (p : ℝ≥0) (a : ℝ) : Prop :=
  0 ≤ a ∧ ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, glyzDyadicSquareConstant m N p ≤ C * (2 : ℝ) ^ (a * N)

theorem glyz_admissible_square_loss_one (m : ℕ) (p : ℝ≥0) (hp : 1 ≤ p) :
    GlyzAdmissibleSquareLoss m p 1 := by
  refine ⟨by norm_num, 1, by norm_num, fun N => ?_⟩
  simpa using glyzDyadicSquareConstant_le_trivial m N p hp

theorem glyz_admissible_square_loss_mono {m : ℕ} {p : ℝ≥0} {a b : ℝ}
    (ha : GlyzAdmissibleSquareLoss m p a) (hab : a ≤ b) :
    GlyzAdmissibleSquareLoss m p b := by
  rcases ha with ⟨ha, C, hC, h⟩
  refine ⟨ha.trans hab, C, hC, fun N => (h N).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg N))) hC.le

def glyzOptimalSquareLoss (m : ℕ) (p : ℝ≥0) : ℝ :=
  sInf {a : ℝ | GlyzAdmissibleSquareLoss m p a}

theorem glyz_admissible_square_losses_nonempty (m : ℕ) (p : ℝ≥0) (hp : 1 ≤ p) :
    {a : ℝ | GlyzAdmissibleSquareLoss m p a}.Nonempty :=
  ⟨1, glyz_admissible_square_loss_one m p hp⟩

theorem glyz_admissible_square_losses_bddBelow (m : ℕ) (p : ℝ≥0) :
    BddBelow {a : ℝ | GlyzAdmissibleSquareLoss m p a} :=
  ⟨0, fun _ ha => ha.1⟩

theorem glyzOptimalSquareLoss_nonneg (m : ℕ) (p : ℝ≥0) (hp : 1 ≤ p) :
    0 ≤ glyzOptimalSquareLoss m p :=
  le_csInf (glyz_admissible_square_losses_nonempty m p hp) fun _ ha => ha.1

theorem glyzOptimalSquareLoss_le {m : ℕ} {p : ℝ≥0} {a : ℝ}
    (ha : GlyzAdmissibleSquareLoss m p a) :
    glyzOptimalSquareLoss m p ≤ a :=
  csInf_le (glyz_admissible_square_losses_bddBelow m p) ha

theorem glyzOptimalSquareLoss_le_one (m : ℕ) (p : ℝ≥0) (hp : 1 ≤ p) :
    glyzOptimalSquareLoss m p ≤ 1 :=
  glyzOptimalSquareLoss_le (glyz_admissible_square_loss_one m p hp)

/-- Every exponent strictly above the infimum is genuinely admissible;
no endpoint attainment is assumed. -/
theorem glyz_admissible_square_loss_of_optimal_lt (m : ℕ) (p : ℝ≥0) (hp : 1 ≤ p)
    {a : ℝ} (ha : glyzOptimalSquareLoss m p < a) :
    GlyzAdmissibleSquareLoss m p a := by
  obtain ⟨b, hb, hba⟩ := exists_lt_of_csInf_lt
    (glyz_admissible_square_losses_nonempty m p hp) ha
  exact glyz_admissible_square_loss_mono hb hba.le

theorem glyz_admissible_square_loss_add_epsilon (m : ℕ) (p : ℝ≥0) (hp : 1 ≤ p)
    {ε : ℝ} (hε : 0 < ε) :
    GlyzAdmissibleSquareLoss m p (glyzOptimalSquareLoss m p + ε) :=
  glyz_admissible_square_loss_of_optimal_lt m p hp (by linarith)

/-- A feasible exponent gives an estimate on the actual Fourier-supported
sum, uniformly in depth and in the whole family. -/
theorem glyz_dyadic_decoupling_of_admissible_square_loss {m : ℕ} {p : ℝ≥0}
    (hp : 1 ≤ p) {a : ℝ} (ha : GlyzAdmissibleSquareLoss m p a) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ f : ℕ → SchwartzMap (GlyzSpace m) ℂ,
      GlyzDyadicSupported m N f →
      lpNorm (fun x => ∑ i ∈ Finset.range (2 ^ N), f i x) p volume ^ (2 : ℕ) ≤
        C * (2 : ℝ) ^ (a * N) * glyzDyadicSquareEnergy m N p f := by
  obtain ⟨_, C, hC, h⟩ := ha
  refine ⟨C, hC, fun N f hf => ?_⟩
  exact ((glyzDyadicSquareConstant_bound m N p hp).2 f hf).trans
    (mul_le_mul_of_nonneg_right (h N) (glyzDyadicSquareEnergy_nonneg m N p f))

/-- Vanishing optimal loss is exactly the all-epsilon dyadic decoupling
statement. This equivalence exposes the remaining analytic conclusion
instead of declaring it proved by the definition of the infimum. -/
theorem glyzOptimalSquareLoss_eq_zero_iff (m : ℕ) (p : ℝ≥0) (hp : 1 ≤ p) :
    glyzOptimalSquareLoss m p = 0 ↔
      ∀ ε : ℝ, 0 < ε → GlyzAdmissibleSquareLoss m p ε := by
  constructor
  · intro h ε hε
    apply glyz_admissible_square_loss_of_optimal_lt m p hp
    simpa only [h] using hε
  · intro h
    apply le_antisymm _ (glyzOptimalSquareLoss_nonneg m p hp)
    apply le_of_forall_pos_le_add
    intro ε hε
    simpa using glyzOptimalSquareLoss_le (h ε hε)

end PlanarNikodym
