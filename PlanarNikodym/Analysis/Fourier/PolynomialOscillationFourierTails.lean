import PlanarNikodym.Analysis.Fourier.UniformFourierMoments

/-! Fourier tails with explicit polynomial dependence on oscillation.
The required derivative order is the tail order plus one fixed
dimension-dependent integer, which is essential for scale iteration. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform
namespace PlanarNikodym

variable {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_uniform_polynomial_derivative_integral
    (S : P → ℝ → SchwartzMap E ℂ) {K : Set E} (hK : IsCompact K)
    (hs : ∀ p α, tsupport (S p α) ⊆ K)
    (hj : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p α x,
      ‖iteratedFDeriv ℝ n (S p α) x‖ ≤ B * (1 + |α|) ^ n)
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p α,
      (∫ x, ‖iteratedFDeriv ℝ n (S p α) x‖) ≤ C * (1 + |α|) ^ n := by
  obtain ⟨B, hB, hb⟩ := hj n
  let S' : P × ℝ → SchwartzMap E ℂ := fun q => S q.1 q.2
  let B' : P × ℝ → ℝ := fun q => B * (1 + |q.2|) ^ n
  have hB' (q : P × ℝ) : 0 ≤ B' q := by dsimp only [B']; positivity
  obtain ⟨C₀, hC₀, h₀⟩ := exists_uniform_schwartz_seminorm_bound
    S' hK (fun q => hs q.1 q.2) n 0 B' hB' (fun q => hb q.1 q.2)
  obtain ⟨C₁, hC₁, h₁⟩ := exists_uniform_schwartz_seminorm_bound
    S' hK (fun q => hs q.1 q.2) n (volume : Measure E).integrablePower
    B' hB' (fun q => hb q.1 q.2)
  let Z : ℝ := 2 ^ (volume : Measure E).integrablePower *
    ∫ x : E, (1 + ‖x‖) ^ (-((volume : Measure E).integrablePower : ℝ))
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  refine ⟨Z * (C₀ + C₁) * B, by positivity, fun p α => ?_⟩
  have hh := (S p α).integral_pow_mul_iteratedFDeriv_le ℝ volume 0 n
  simp only [pow_zero, one_mul, zero_add] at hh
  apply hh.trans
  have hs' := mul_le_mul_of_nonneg_left (add_le_add (h₀ (p, α)) (h₁ (p, α))) hZ
  exact hs'.trans_eq (by dsimp [B']; ring)

theorem exists_uniform_polynomial_fourier_seminorm
    (S : P → ℝ → SchwartzMap E ℂ) {K : Set E} (hK : IsCompact K)
    (hs : ∀ p α, tsupport (S p α) ⊆ K)
    (hj : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p α x,
      ‖iteratedFDeriv ℝ n (S p α) x‖ ≤ B * (1 + |α|) ^ n)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p α,
      SchwartzMap.seminorm ℝ k 0 (𝓕 (S p α)) ≤ C * (1 + |α|) ^ k := by
  choose D hD hd using exists_uniform_polynomial_derivative_integral S hK hs hj
  let C : ℝ := 2 ^ k * ∑ j ∈ Finset.range (k + 1), D j
  refine ⟨C, mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => hD j),
    fun p α => ?_⟩
  apply SchwartzMap.seminorm_le_bound ℝ k 0 (𝓕 (S p α)) (by
    exact mul_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => hD j))
      (by positivity))
  intro ξ
  have hh := Real.pow_mul_norm_iteratedFDeriv_fourier_le ((S p α).smooth ⊤)
    (fun a b _ _ => (S p α).integrable_pow_mul_iteratedFDeriv volume a b)
    (k := 0) (n := k) (by exact_mod_cast le_top) (by exact_mod_cast le_top) ξ
  have hh' : ‖ξ‖ ^ k * ‖𝓕 (S p α) ξ‖ ≤
      2 ^ k * ∑ j ∈ Finset.range (k + 1), ∫ x, ‖iteratedFDeriv ℝ j (S p α) x‖ := by
    simpa only [pow_zero, Nat.cast_zero, mul_zero, zero_add, one_mul, Finset.sum_product,
      SchwartzMap.fourier_coe,
      Finset.range_one, Finset.sum_singleton, norm_iteratedFDeriv_zero] using hh
  simp only [norm_iteratedFDeriv_zero]
  apply hh'.trans
  calc
    _ ≤ 2 ^ k * ∑ j ∈ Finset.range (k + 1), D j * (1 + |α|) ^ k := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j hj'
      exact (hd j p α).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by linarith [abs_nonneg α])
          (Nat.le_of_lt_succ (Finset.mem_range.mp hj'))) (hD j))
    _ = C * (1 + |α|) ^ k := by rw [← Finset.sum_mul]; ring

theorem exists_uniform_polynomial_fourier_moment
    (S : P → ℝ → SchwartzMap E ℂ) {K : Set E} (hK : IsCompact K)
    (hs : ∀ p α, tsupport (S p α) ⊆ K)
    (hj : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p α x,
      ‖iteratedFDeriv ℝ n (S p α) x‖ ≤ B * (1 + |α|) ^ n)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p α,
      (∫ ξ, ‖ξ‖ ^ k * ‖𝓕 (S p α) ξ‖) ≤
        C * (1 + |α|) ^ (k + (volume : Measure E).integrablePower) := by
  obtain ⟨C₀, hC₀, h₀⟩ := exists_uniform_polynomial_fourier_seminorm S hK hs hj 0
  obtain ⟨C₁, hC₁, h₁⟩ := exists_uniform_polynomial_fourier_seminorm
    S hK hs hj (k + (volume : Measure E).integrablePower)
  let Z : ℝ := 2 ^ (volume : Measure E).integrablePower *
    ∫ x : E, (1 + ‖x‖) ^ (-((volume : Measure E).integrablePower : ℝ))
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  refine ⟨Z * (C₀ + C₁), by positivity, fun p α => ?_⟩
  have hh := (𝓕 (S p α)).integral_pow_mul_iteratedFDeriv_le ℝ volume k 0
  simp only [norm_iteratedFDeriv_zero] at hh
  have h₀' : SchwartzMap.seminorm ℝ 0 0 (𝓕 (S p α)) ≤
      C₀ * (1 + |α|) ^ (k + (volume : Measure E).integrablePower) := by
    have hh₀ := h₀ p α
    simp only [pow_zero, mul_one] at hh₀
    exact hh₀.trans (le_mul_of_one_le_right hC₀
      (one_le_pow₀ (by linarith [abs_nonneg α])))
  exact hh.trans ((mul_le_mul_of_nonneg_left (add_le_add h₀' (h₁ p α)) hZ).trans_eq (by ring))

/-- At cutoff radius `(1+|α|)T`, every extra power of `T` costs one
derivative, while the remaining oscillation loss is one fixed power. -/
theorem exists_uniform_polynomial_fourier_tail
    (S : P → ℝ → SchwartzMap E ℂ) {K : Set E} (hK : IsCompact K)
    (hs : ∀ p α, tsupport (S p α) ⊆ K)
    (hj : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p α x,
      ‖iteratedFDeriv ℝ n (S p α) x‖ ≤ B * (1 + |α|) ^ n)
    (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p α T, 0 < T →
      (∫ ξ in {ξ : E | (1 + |α|) * T ≤ ‖ξ‖}, ‖𝓕 (S p α) ξ‖) ≤
        C * (1 + |α|) ^ (volume : Measure E).integrablePower * (T⁻¹) ^ M := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_polynomial_fourier_moment S hK hs hj M
  refine ⟨C, hC, fun p α T hT => ?_⟩
  have hα : 0 < 1 + |α| := by positivity
  have ht := schwartz_integral_moment_tail_le volume (𝓕 (S p α)) 0 M (mul_pos hα hT)
  simp only [pow_zero, one_mul, zero_add] at ht
  apply ht.trans
  apply (mul_le_mul_of_nonneg_left (hb p α) (by positivity)).trans_eq
  rw [pow_add, mul_inv_rev, mul_pow]
  have hc : (1 + |α|)⁻¹ ^ M * (1 + |α|) ^ M = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hα.ne', one_pow]
  calc
    _ = C * ((1 + |α|)⁻¹ ^ M * (1 + |α|) ^ M) *
        (1 + |α|) ^ (volume : Measure E).integrablePower * (T⁻¹) ^ M := by ring
    _ = _ := by rw [hc, mul_one]

end PlanarNikodym
