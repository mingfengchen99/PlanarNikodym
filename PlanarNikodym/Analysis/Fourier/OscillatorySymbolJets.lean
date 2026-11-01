import PlanarNikodym.Analysis.Fourier.FrozenAmplitudeFamily
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Quantitative symbol bounds for arbitrary oscillation size. The
`n`-th actual derivative grows at most like `(1+|α|)^n`, so large Taylor
remainders can be treated without assuming that their size is at most one. -/
noncomputable section
open Set
open scoped ContDiff
namespace PlanarNikodym

def unitImaginaryExponential (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

theorem contDiff_unitImaginaryExponential : ContDiff ℝ ∞ unitImaginaryExponential :=
  (Complex.ofRealCLM.contDiff.mul contDiff_const).cexp

theorem iteratedDeriv_unitImaginaryExponential (n : ℕ) :
    iteratedDeriv n unitImaginaryExponential =
      fun t => Complex.I ^ n * unitImaginaryExponential t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have h := (((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).cexp).const_mul
      (Complex.I ^ n)
    simpa only [unitImaginaryExponential, Complex.ofRealCLM_apply, Complex.ofReal_one,
      one_mul, mul_one, pow_succ, mul_assoc, mul_comm, mul_left_comm] using h.deriv

theorem norm_iteratedFDeriv_unitImaginaryExponential (n : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ n unitImaginaryExponential t‖ = 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_unitImaginaryExponential]
  simp only [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul,
    unitImaginaryExponential, Complex.norm_exp_ofReal_mul_I]

theorem norm_iteratedFDeriv_oscillatoryPhase_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : E → ℝ} (hH : ContDiff ℝ ∞ H) (n : ℕ) (x : E)
    {D : ℝ} (hD : 1 ≤ D)
    (hb : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i H x‖ ≤ D)
    (α : ℝ) :
    ‖iteratedFDeriv ℝ n (fun z => unitImaginaryExponential (α * H z)) x‖ ≤
      ((n.factorial : ℝ) * D ^ n) * (1 + |α|) ^ n := by
  have hs : ContDiff ℝ ∞ (fun z => α * H z) := contDiff_const.mul hH
  have hh := norm_iteratedFDeriv_comp_le contDiff_unitImaginaryExponential hs
    (n := n) (by exact_mod_cast le_top) x
    (C := 1) (D := D * (1 + |α|))
    (fun i _ => (norm_iteratedFDeriv_unitImaginaryExponential i _).le) (by
      intro i hi hin
      have he : iteratedFDeriv ℝ i (fun z => α * H z) x =
          α • iteratedFDeriv ℝ i H x :=
        by
          simpa only [smul_eq_mul] using iteratedFDeriv_const_smul_apply'
            (a := α) (i := i) (x := x)
            (hH.of_le (by exact_mod_cast le_top)).contDiffAt
      rw [he, norm_smul, Real.norm_eq_abs]
      calc
        _ ≤ |α| * D := mul_le_mul_of_nonneg_left (hb i hi hin) (abs_nonneg _)
        _ ≤ D * (1 + |α|) := by nlinarith [abs_nonneg α]
        _ ≤ (D * (1 + |α|)) ^ i := le_self_pow₀
          (by nlinarith [abs_nonneg α]) (by omega))
  simpa only [Function.comp_def, mul_one, mul_pow, mul_assoc] using hh

/-- Uniform actual phase jets imply polynomial, rather than unspecified,
growth in the oscillation parameter. -/
theorem exists_uniform_oscillatoryPhase_jet_bound
    {P E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : P → E → ℝ) (hH : ∀ p, ContDiff ℝ ∞ (H p))
    (hjet : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p x, ‖iteratedFDeriv ℝ n (H p) x‖ ≤ B)
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p α x,
      ‖iteratedFDeriv ℝ n (fun z => unitImaginaryExponential (α * H p z)) x‖ ≤
        C * (1 + |α|) ^ n := by
  choose B hB hb using hjet
  let D := 1 + ∑ i ∈ Finset.range (n + 1), B i
  have hD : 1 ≤ D := by
    dsimp only [D]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hB i)
  have hB' (i : ℕ) (hi : i ≤ n) : B i ≤ D := by
    apply (Finset.single_le_sum (s := Finset.range (n + 1)) (f := B)
      (fun j _ => hB j) (Finset.mem_range.mpr (by omega : i < n + 1))).trans
    dsimp only [D]
    linarith
  refine ⟨n.factorial * D ^ n, by positivity, fun p α x => ?_⟩
  exact norm_iteratedFDeriv_oscillatoryPhase_le (hH p) n x hD
    (fun i _ hi => (hb i p x).trans (hB' i hi)) α

def oscillatorySymbol {P E : Type*} (A : P → E → ℂ) (H : P → E → ℝ)
    (p : P) (α : ℝ) (x : E) : ℂ :=
  A p x * unitImaginaryExponential (α * H p x)

theorem exists_uniform_oscillatorySymbol_jet_bound
    {P E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : P → E → ℂ) (H : P → E → ℝ)
    (hA : ∀ p, ContDiff ℝ ∞ (A p)) (hH : ∀ p, ContDiff ℝ ∞ (H p))
    (hAj : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p x, ‖iteratedFDeriv ℝ n (A p) x‖ ≤ B)
    (hHj : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p x, ‖iteratedFDeriv ℝ n (H p) x‖ ≤ B)
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p α x,
      ‖iteratedFDeriv ℝ n (oscillatorySymbol A H p α) x‖ ≤ C * (1 + |α|) ^ n := by
  choose B hB hb using hAj
  choose D hD hd using exists_uniform_oscillatoryPhase_jet_bound H hH hHj
  let C := ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * B i * D (n - i)
  refine ⟨C, Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB i)) (hD (n - i))), fun p α x => ?_⟩
  have hphase : ContDiff ℝ ∞ (fun z => unitImaginaryExponential (α * H p z)) :=
    contDiff_unitImaginaryExponential.comp (contDiff_const.mul (hH p))
  apply (norm_iteratedFDeriv_mul_le (hA p) hphase x
    (n := n) (by exact_mod_cast le_top)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        ((n.choose i : ℝ) * B i * D (n - i)) * (1 + |α|) ^ n := by
      apply Finset.sum_le_sum
      intro i _
      have hB0 := hB i
      have hD0 := hD (n - i)
      have hpow : (1 + |α|) ^ (n - i) ≤ (1 + |α|) ^ n :=
        pow_le_pow_right₀ (by linarith [abs_nonneg α]) (Nat.sub_le _ _)
      calc
        _ ≤ (n.choose i : ℝ) * B i * (D (n - i) * (1 + |α|) ^ (n - i)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hb i p x) (by positivity))
            (hd (n - i) p α x) (norm_nonneg _) (by positivity)
        _ ≤ ((n.choose i : ℝ) * B i * D (n - i)) * (1 + |α|) ^ n := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = C * (1 + |α|) ^ n := (Finset.sum_mul ..).symm

end PlanarNikodym
