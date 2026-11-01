import PlanarNikodym.Analysis.Fourier.GlyzFourierProjector
import PlanarNikodym.Analysis.Localization.FiniteCutoffPartition
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Algebra.Order.Chebyshev

/-! A compact frequency region has an actual finite smooth Fourier
partition subordinate to any open cover. The resulting Schwartz
operators preserve original supports, sum to the identity, and have
uniform Lp bounds for every p at least one. -/
noncomputable section
open Set MeasureTheory FourierTransform
open scoped FourierTransform ENNReal NNReal BigOperators
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem glyzFourierProjector_lpNorm_le (χ f : SchwartzMap E ℂ)
    {p : ℝ≥0} (hp : 1 ≤ p) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : (∫ x, ‖glyzReproducingKernel χ x‖) ≤ M) :
    lpNorm (glyzFourierProjector χ f : E → ℂ) p volume ≤
      M * lpNorm (f : E → ℂ) p volume := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp0' : (0 : ℝ) < p := hp0
  have h := glyzFourierProjector_power_integral_le χ f hp hM0 hM
  rw [← eLpNorm_nnreal_pow_eq_lintegral hp0.ne',
    ← eLpNorm_nnreal_pow_eq_lintegral hp0.ne', ← ENNReal.mul_rpow_of_nonneg _ _ hp0'.le] at h
  have hnorm := (ENNReal.rpow_le_rpow_iff hp0').mp h
  rw [← ofReal_lpNorm ((glyzFourierProjector χ f).memLp p volume),
    ← ofReal_lpNorm (f.memLp p volume), ← ENNReal.ofReal_mul hM0] at hnorm
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hM0 lpNorm_nonneg)).mp hnorm

theorem support_fourier_glyzFourierProjector_inter (χ f : SchwartzMap E ℂ) :
    Function.support (𝓕 (glyzFourierProjector χ f : E → ℂ)) ⊆
      Function.support (𝓕 (f : E → ℂ)) ∩ Function.support χ := by
  intro ξ hξ
  simpa only [Function.mem_support, mem_inter_iff, fourier_glyzFourierProjector,
    mul_ne_zero_iff] using hξ

theorem glyzFourierProjector_sum_reproduces {ι : Type*} [Fintype ι]
    (χ : ι → SchwartzMap E ℂ) (f : SchwartzMap E ℂ)
    (hχ : ∀ ξ ∈ Function.support (𝓕 (f : E → ℂ)), ∑ i, χ i ξ = 1) :
    ∑ i, glyzFourierProjector (χ i) f = f := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap E ℂ)).injective
  ext ξ
  simp only [FourierTransform.fourierEquiv_apply, FourierTransform.fourier_sum, sum_apply]
  simp_rw [SchwartzMap.fourier_coe, fourier_glyzFourierProjector]
  rw [← Finset.mul_sum]
  by_cases hξ : 𝓕 (f : E → ℂ) ξ = 0
  · simp [hξ]
  · rw [hχ ξ hξ, mul_one]

theorem exists_glyz_finite_fourier_partition {ι : Type*} (K : Set E)
    (hK : IsCompact K) (U : ι → Set E) (hU : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i, U i) :
    ∃ (S : Finset ι) (χ : S → SchwartzMap E ℂ) (M : ℝ), 0 < M ∧
      (∀ i, Function.support (χ i) ⊆ U i) ∧
      (∀ ξ ∈ K, ∑ i : S, χ i ξ = 1) ∧
      (∀ f : SchwartzMap E ℂ,
        Function.support (𝓕 (f : E → ℂ)) ⊆ K →
        ∑ i : S, glyzFourierProjector (χ i) f = f) ∧
      (∀ (p : ℝ≥0), 1 ≤ p → ∀ (i : S) (f : SchwartzMap E ℂ),
        lpNorm (glyzFourierProjector (χ i) f : E → ℂ) p volume ≤
          M * lpNorm (f : E → ℂ) p volume) := by
  classical
  obtain ⟨η, N, hη, hcη, hrη, _, hKN, hNη, hηU⟩ :=
    exists_compact_smooth_cutoff hK (isOpen_iUnion hU) hcover
  obtain ⟨S, ψ, hψ, hsum⟩ := exists_finite_cutoff_partition η hη hcη
    (fun x => (hrη x).1) U hU hηU
  let χ : S → SchwartzMap E ℂ := fun i =>
    ((hψ i).2.1.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (hψ i).1)
  let b : S → ℝ := fun i => ∫ x, ‖glyzReproducingKernel (χ i) x‖
  have hb (i : S) : 0 ≤ b i := integral_nonneg fun _ => norm_nonneg _
  let M : ℝ := 1 + ∑ i : S, b i
  have hM : 0 < M := by dsimp [M]; positivity
  have hχsum (ξ : E) (hξ : ξ ∈ K) : ∑ i : S, χ i ξ = 1 := by
    change (∑ i : S, (ψ i ξ : ℂ)) = 1
    rw [← Complex.ofReal_sum, hsum, hNη ξ (hKN hξ)]
    rfl
  refine ⟨S, χ, M, hM, ?_, hχsum, ?_, ?_⟩
  · intro i ξ hξ
    apply (hψ i).2.2.2.1
    apply subset_tsupport
    intro hz
    apply hξ
    change (ψ i ξ : ℂ) = 0
    rw [hz, Complex.ofReal_zero]
  · intro f hf
    exact glyzFourierProjector_sum_reproduces χ f (fun ξ hξ => hχsum ξ (hf hξ))
  · intro p hp i f
    apply glyzFourierProjector_lpNorm_le (χ i) f hp hM.le
    change b i ≤ 1 + ∑ j : S, b j
    exact (Finset.single_le_sum (fun j _ => hb j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)

theorem glyz_finite_schwartz_square_sum_le {ι : Type*} (I : Finset ι)
    (f : ι → SchwartzMap E ℂ) {p : ℝ≥0} (hp : 1 ≤ p) :
    lpNorm ((∑ i ∈ I, f i : SchwartzMap E ℂ) : E → ℂ) p volume ^ 2 ≤
      (I.card : ℝ) * ∑ i ∈ I, lpNorm (f i : E → ℂ) p volume ^ 2 := by
  have hsum : lpNorm ((∑ i ∈ I, f i : SchwartzMap E ℂ) : E → ℂ) p volume ≤
      ∑ i ∈ I, lpNorm (f i : E → ℂ) p volume := by
    have h := lpNorm_sum_le (s := I) (fun i _ => (f i).memLp p volume)
      (show (1 : ℝ≥0∞) ≤ (p : ℝ≥0∞) by exact_mod_cast hp)
    convert h using 1
    congr 1
    ext x
    simp
  exact (pow_le_pow_left₀ lpNorm_nonneg hsum 2).trans sq_sum_le_card_mul_sum_sq

/-- Reassemble finitely many bounded projections. Only the fixed number
of projections is paid, independently of the angular index set. -/
theorem glyz_finite_projection_decoupling {ι κ : Type*} [Fintype κ]
    (I : Finset ι) (f : ι → SchwartzMap E ℂ)
    (P : κ → SchwartzMap E ℂ →ₗ[ℂ] SchwartzMap E ℂ)
    {p : ℝ≥0} (hp : 1 ≤ p) {D M : ℝ} (hD : 0 ≤ D)
    (hreconstruct : ∀ i ∈ I, ∑ a : κ, P a (f i) = f i)
    (hbound : ∀ a i, i ∈ I →
      lpNorm (P a (f i) : E → ℂ) p volume ≤ M * lpNorm (f i : E → ℂ) p volume)
    (hdec : ∀ a, lpNorm ((∑ i ∈ I, P a (f i) : SchwartzMap E ℂ) : E → ℂ)
        p volume ^ 2 ≤ D * ∑ i ∈ I, lpNorm (P a (f i) : E → ℂ) p volume ^ 2) :
    lpNorm ((∑ i ∈ I, f i : SchwartzMap E ℂ) : E → ℂ) p volume ^ 2 ≤
      ((Fintype.card κ : ℝ) * M) ^ 2 * D *
        ∑ i ∈ I, lpNorm (f i : E → ℂ) p volume ^ 2 := by
  have hsum : (∑ i ∈ I, f i) = ∑ a : κ, ∑ i ∈ I, P a (f i) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i hi => (hreconstruct i hi).symm
  have hpiece (a : κ) :
      lpNorm ((∑ i ∈ I, P a (f i) : SchwartzMap E ℂ) : E → ℂ) p volume ^ 2 ≤
        D * M ^ 2 * ∑ i ∈ I, lpNorm (f i : E → ℂ) p volume ^ 2 := by
    apply (hdec a).trans
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hD
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa only [mul_pow] using pow_le_pow_left₀ lpNorm_nonneg (hbound a i hi) 2
  calc
    _ = lpNorm ((∑ a : κ, ∑ i ∈ I, P a (f i) : SchwartzMap E ℂ) : E → ℂ)
        p volume ^ 2 := by rw [hsum]
    _ ≤ (Fintype.card κ : ℝ) *
        ∑ a : κ, lpNorm ((∑ i ∈ I, P a (f i) : SchwartzMap E ℂ) : E → ℂ)
          p volume ^ 2 := by
      simpa using glyz_finite_schwartz_square_sum_le Finset.univ
        (fun a => ∑ i ∈ I, P a (f i)) hp
    _ ≤ (Fintype.card κ : ℝ) * ∑ _a : κ,
        D * M ^ 2 * ∑ i ∈ I, lpNorm (f i : E → ℂ) p volume ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hpiece a) (by positivity)
    _ = _ := by simp; ring

end PlanarNikodym
