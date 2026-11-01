import PlanarNikodym.Analysis.Fourier.BandOscillatoryRepresentation
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Uniform full-derivative bounds for the actual positive-sign character
appearing in the inverse Fourier integral. -/
noncomputable section
open Set
open scoped ContDiff

namespace PlanarNikodym

/-- Full derivatives of the exponential of a complex-valued real linear
functional grow at most by one operator norm at each derivative. -/
theorem norm_iteratedFDeriv_cexp_clm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℂ) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y => Complex.exp (L y)) x‖ ≤
      ‖L‖ ^ j * ‖Complex.exp (L x)‖ := by
  let f : E → ℂ := fun y => Complex.exp (L y)
  have hf : ContDiff ℝ ∞ f := L.contDiff.cexp
  let M : ℂ →L[ℝ] (E →L[ℝ] ℂ) :=
    (ContinuousLinearMap.toSpanSingleton ℂ L).restrictScalars ℝ
  have hM : ‖M‖ ≤ ‖L‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
    intro z
    change ‖z • L‖ ≤ ‖L‖ * ‖z‖
    rw [norm_smul, mul_comm]
  have hdf : fderiv ℝ f = M ∘ f := by
    funext y
    exact L.hasFDerivAt.cexp.fderiv
  change ‖iteratedFDeriv ℝ j f x‖ ≤ ‖L‖ ^ j * ‖f x‖
  induction j with
  | zero => simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul]; exact le_rfl
  | succ j ih =>
    rw [← norm_iteratedFDeriv_fderiv, hdf]
    calc
      ‖iteratedFDeriv ℝ j (M ∘ f) x‖ ≤ ‖M‖ * ‖iteratedFDeriv ℝ j f x‖ :=
        M.norm_iteratedFDeriv_comp_left (contDiff_infty.mp hf j).contDiffAt le_rfl
      _ ≤ ‖L‖ * (‖L‖ ^ j * ‖f x‖) := by gcongr
      _ = ‖L‖ ^ (j + 1) * ‖f x‖ := by rw [pow_succ]; ring

/-- The real phase as a continuous real linear functional. -/
def fourierPhaseCLM (ξ : Plane) : Plane →L[ℝ] ℝ :=
  ξ.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + ξ.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem fourierPhaseCLM_apply (ξ x : Plane) :
    fourierPhaseCLM ξ x = fourierPhase x ξ := by
  change ξ.1 * x.1 + ξ.2 * x.2 = x.1 * ξ.1 + x.2 * ξ.2
  ring

/-- The actual exponent, including the inverse-transform sign and `2π`. -/
def fourierCharacterExponent (ξ : Plane) : Plane →L[ℝ] ℂ :=
  (((2 * Real.pi : ℝ) : ℂ) * Complex.I) •
    (Complex.ofRealCLM.comp (fourierPhaseCLM ξ))

@[simp] theorem fourierCharacterExponent_apply (ξ x : Plane) :
    fourierCharacterExponent ξ x =
      (((2 * Real.pi * fourierPhase x ξ : ℝ) : ℂ) * Complex.I) := by
  simp only [fourierCharacterExponent, smul_apply,
    ContinuousLinearMap.comp_apply, fourierPhaseCLM_apply, Complex.ofRealCLM_apply,
    smul_eq_mul, Complex.ofReal_mul]
  ring

theorem planeFourierCharacter_contDiff (ξ : Plane) :
    ContDiff ℝ ∞ (fun x => planeFourierCharacter x ξ) := by
  have he : (fun x => planeFourierCharacter x ξ) =
      fun x => Complex.exp (fourierCharacterExponent ξ x) := by
    funext x
    rw [fourierCharacterExponent_apply]
    rfl
  rw [he]
  exact (fourierCharacterExponent ξ).contDiff.cexp

theorem norm_fourierCharacterExponent_le (ξ : Plane) :
    ‖fourierCharacterExponent ξ‖ ≤ 2 * Real.pi * (|ξ.1| + |ξ.2|) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  rw [fourierCharacterExponent_apply]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos Real.pi_pos]
  have hphase : |fourierPhase x ξ| ≤ (|ξ.1| + |ξ.2|) * ‖x‖ := by
    unfold fourierPhase
    calc
      |x.1 * ξ.1 + x.2 * ξ.2| ≤ |x.1 * ξ.1| + |x.2 * ξ.2| := abs_add_le _ _
      _ = |ξ.1| * ‖x.1‖ + |ξ.2| * ‖x.2‖ := by simp only [abs_mul, Real.norm_eq_abs]; ring
      _ ≤ |ξ.1| * ‖x‖ + |ξ.2| * ‖x‖ := by
        gcongr
        · exact norm_fst_le x
        · exact norm_snd_le x
      _ = (|ξ.1| + |ξ.2|) * ‖x‖ := by ring
  nlinarith [mul_le_mul_of_nonneg_left hphase
    (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos).le]

/-- Every full multilinear jet has the expected polynomial frequency
bound. This uses the original product norm on `Plane`. -/
theorem norm_iteratedFDeriv_planeFourierCharacter_le (ξ x : Plane) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y => planeFourierCharacter y ξ) x‖ ≤
      (2 * Real.pi * (|ξ.1| + |ξ.2|)) ^ j := by
  have he : (fun y => Complex.exp (fourierCharacterExponent ξ y)) =
      fun y => planeFourierCharacter y ξ := by
    funext y
    rw [fourierCharacterExponent_apply]
    rfl
  have h := norm_iteratedFDeriv_cexp_clm_le (fourierCharacterExponent ξ) j x
  rw [he, show Complex.exp (fourierCharacterExponent ξ x) = planeFourierCharacter x ξ by
    exact congrFun he x, norm_planeFourierCharacter, mul_one] at h
  exact h.trans (pow_le_pow_left₀ (norm_nonneg _) (norm_fourierCharacterExponent_le ξ) j)

/-- A common bound for every order in a fixed finite jet. -/
theorem norm_iteratedFDeriv_planeFourierCharacter_le_of_le
    (ξ x : Plane) {j s : ℕ} (hjs : j ≤ s) :
    ‖iteratedFDeriv ℝ j (fun y => planeFourierCharacter y ξ) x‖ ≤
      (1 + 2 * Real.pi * (|ξ.1| + |ξ.2|)) ^ s := by
  refine (norm_iteratedFDeriv_planeFourierCharacter_le ξ x j).trans ?_
  have hC : 0 ≤ 2 * Real.pi * (|ξ.1| + |ξ.2|) := by positivity
  calc
    (2 * Real.pi * (|ξ.1| + |ξ.2|)) ^ j ≤
        (1 + 2 * Real.pi * (|ξ.1| + |ξ.2|)) ^ j :=
      pow_le_pow_left₀ hC (by linarith) j
    _ ≤ (1 + 2 * Real.pi * (|ξ.1| + |ξ.2|)) ^ s :=
      pow_le_pow_right₀ (by linarith) hjs

/-- Polynomial frequency growth for the whole finite jet, uniformly in
the spatial point. The displayed coefficient depends only on `s`. -/
theorem sum_norm_iteratedFDeriv_planeFourierCharacter_le
    (ξ x : Plane) (s : ℕ) :
    (∑ j ∈ Finset.range (s + 1),
      ‖iteratedFDeriv ℝ j (fun y => planeFourierCharacter y ξ) x‖) ≤
      ((s + 1 : ℕ) : ℝ) * (1 + 4 * Real.pi) ^ s * (1 + ‖ξ‖) ^ s := by
  have hξ : |ξ.1| + |ξ.2| ≤ 2 * ‖ξ‖ := by
    have h₁ : |ξ.1| ≤ ‖ξ‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le ξ
    have h₂ : |ξ.2| ≤ ‖ξ‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le ξ
    linarith
  have hb : 1 + 2 * Real.pi * (|ξ.1| + |ξ.2|) ≤
      (1 + 4 * Real.pi) * (1 + ‖ξ‖) := by
    have hmul := mul_le_mul_of_nonneg_left hξ
      (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos).le
    nlinarith [norm_nonneg ξ, Real.pi_pos]
  calc
    (∑ j ∈ Finset.range (s + 1),
        ‖iteratedFDeriv ℝ j (fun y => planeFourierCharacter y ξ) x‖) ≤
        ∑ _j ∈ Finset.range (s + 1),
          (1 + 2 * Real.pi * (|ξ.1| + |ξ.2|)) ^ s := by
      apply Finset.sum_le_sum
      intro j hj
      exact norm_iteratedFDeriv_planeFourierCharacter_le_of_le ξ x
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    _ = ((s + 1 : ℕ) : ℝ) *
        (1 + 2 * Real.pi * (|ξ.1| + |ξ.2|)) ^ s := by simp
    _ ≤ ((s + 1 : ℕ) : ℝ) * ((1 + 4 * Real.pi) * (1 + ‖ξ‖)) ^ s := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

end PlanarNikodym
