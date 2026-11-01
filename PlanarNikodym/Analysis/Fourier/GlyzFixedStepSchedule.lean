import PlanarNikodym.Analysis.Fourier.GlyzCurveIterationLoss

/-! Fixed angular-depth schedules. The initial depth absorbs the Taylor
threshold, while a sufficiently large fixed increment absorbs each
uniform one-step constant into an arbitrarily small power loss. -/
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace PlanarNikodym

def glyzFixedDepth (n₀ q N j : ℕ) : ℕ := min N (n₀ + j * q)

theorem glyzFixedDepth_mono (n₀ q N j : ℕ) :
    glyzFixedDepth n₀ q N j ≤ glyzFixedDepth n₀ q N (j + 1) := by
  unfold glyzFixedDepth
  simp only [Nat.add_mul, Nat.one_mul]
  omega

theorem glyzFixedDepth_le (n₀ q N j : ℕ) : glyzFixedDepth n₀ q N j ≤ N := min_le_left _ _

theorem glyzFixedDepth_initial (n₀ q N : ℕ) : glyzFixedDepth n₀ q N 0 = min N n₀ := by
  simp [glyzFixedDepth]

theorem glyzFixedDepth_finest (n₀ q N : ℕ) (hq : 0 < q) :
    glyzFixedDepth n₀ q N (N / q + 1) = N := by
  unfold glyzFixedDepth
  have hdiv := Nat.div_add_mod N q
  rw [Nat.mul_comm] at hdiv
  have hmod := Nat.mod_lt N hq
  apply min_eq_left
  simp only [Nat.add_mul, Nat.one_mul]
  omega

theorem glyzFixedDepth_increment (n₀ q N j : ℕ) :
    glyzFixedDepth n₀ q N (j + 1) ≤ glyzFixedDepth n₀ q N j + q := by
  unfold glyzFixedDepth
  simp only [Nat.add_mul, Nat.one_mul]
  omega

theorem glyzFixedDepth_ge (n₀ q N j : ℕ) (hN : n₀ ≤ N) :
    n₀ ≤ glyzFixedDepth n₀ q N j := by
  unfold glyzFixedDepth
  omega

/-- The Taylor threshold holds at every nontrivial step, including the
last truncated step. -/
theorem glyzFixedDepth_taylor_condition (k n₀ q N j : ℕ) (hbase : k * q ≤ n₀) :
    glyzDyadicScale (glyzFixedDepth n₀ q N j) ^ (k + 1) ≤
      glyzDyadicScale (glyzFixedDepth n₀ q N (j + 1)) ^ k := by
  apply glyzDyadicScale_taylor_condition
  by_cases hN : n₀ ≤ N
  · have hinc := Nat.mul_le_mul_left k (glyzFixedDepth_increment n₀ q N j)
    have hge := glyzFixedDepth_ge n₀ q N j hN
    nlinarith
  · have hn : glyzFixedDepth n₀ q N j = N := min_eq_left (by omega)
    have hm : glyzFixedDepth n₀ q N (j + 1) = N := min_eq_left (by omega)
    rw [hn, hm]
    nlinarith

/-- A fixed step can absorb any fixed coefficient. The choice precedes
all finest scales and all functions. -/
theorem exists_glyz_fixed_step_absorbing (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, 0 < q ∧ C ≤ (2 : ℝ) ^ (ε / 2 * q) := by
  have hb : 1 < (2 : ℝ) ^ (ε / 2) := Real.one_lt_rpow (by norm_num) (by positivity)
  obtain ⟨q, hq⟩ := pow_unbounded_of_one_lt (max C 1) hb
  have hqpos : 0 < q := by
    by_contra h
    have hz : q = 0 := by omega
    simp only [hz, pow_zero] at hq
    exact (not_lt_of_ge (le_max_right C 1)) hq
  refine ⟨q, hqpos, (le_max_left _ _).trans (hq.le.trans_eq ?_)⟩
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

theorem glyz_fixed_step_count_bound (N q : ℕ) (_hq : 0 < q) :
    (N / q + 1) * q ≤ N + q := by
  have h := Nat.div_mul_le_self N q
  simp only [Nat.add_mul, Nat.one_mul]
  omega

/-- The product of the fixed-step constants has only epsilon growth;
the one extra final step contributes a single uniform factor. -/
theorem glyz_fixed_step_coefficient_le (n₀ q N : ℕ) (hq : 0 < q)
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (habsorb : C ≤ (2 : ℝ) ^ (ε / 2 * q)) :
    (2 : ℝ) ^ min N n₀ * (C * (2 : ℝ) ^ (ε / 2 * q)) ^ (N / q + 1) ≤
      (2 : ℝ) ^ ((n₀ : ℝ) + ε * q) * (2 : ℝ) ^ (ε * N) := by
  have hstep : C * (2 : ℝ) ^ (ε / 2 * q) ≤ (2 : ℝ) ^ (ε * q) := by
    calc
      _ ≤ (2 : ℝ) ^ (ε / 2 * q) * (2 : ℝ) ^ (ε / 2 * q) :=
        mul_le_mul_of_nonneg_right habsorb (by positivity)
      _ = _ := by rw [← Real.rpow_add (by norm_num)]; congr 1; ring
  have hcount : (ε * q) * (N / q + 1 : ℕ) ≤ ε * ((N : ℝ) + q) := by
    have h := (Nat.cast_le (α := ℝ)).mpr (glyz_fixed_step_count_bound N q hq)
    push_cast at h ⊢
    nlinarith
  calc
    _ ≤ (2 : ℝ) ^ n₀ * ((2 : ℝ) ^ (ε * q)) ^ (N / q + 1) :=
      mul_le_mul (pow_le_pow_right₀ (by norm_num) (min_le_right _ _))
        (pow_le_pow_left₀ (by positivity) hstep _) (by positivity) (by positivity)
    _ = (2 : ℝ) ^ ((n₀ : ℝ) + (ε * q) * (N / q + 1 : ℕ)) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (ε * q)), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_add (by norm_num), Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ ((n₀ : ℝ) + ε * ((N : ℝ) + q)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = _ := by rw [← Real.rpow_add (by norm_num)]; congr 1; ring


/-- Finite fixed-step iteration for actual Schwartz families, in any
finite-dimensional Euclidean ambient space. -/
theorem glyz_fixed_step_iteration {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (n₀ q N : ℕ) (hq : 0 < q) (f : ℕ → SchwartzMap E ℂ)
    (p : ℝ≥0) (hp : 1 ≤ p) {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (habsorb : C ≤ (2 : ℝ) ^ (ε / 2 * q))
    (hstep : ∀ j < N / q + 1, ∀ i < 2 ^ glyzFixedDepth n₀ q N j,
      lpNorm ((glyzDyadicBlock f N (glyzFixedDepth n₀ q N j) i : SchwartzMap E ℂ) : E → ℂ)
        p volume ^ 2 ≤ (C * (2 : ℝ) ^ (ε / 2 * q)) * glyzDyadicBlock
          (fun k => lpNorm ((glyzDyadicBlock f N (glyzFixedDepth n₀ q N (j + 1)) k :
            SchwartzMap E ℂ) : E → ℂ) p volume ^ 2)
          (glyzFixedDepth n₀ q N (j + 1)) (glyzFixedDepth n₀ q N j) i) :
    lpNorm ((∑ i ∈ Finset.range (2 ^ N), f i : SchwartzMap E ℂ) : E → ℂ) p volume ^ 2 ≤
      (2 : ℝ) ^ ((n₀ : ℝ) + ε * q) * (2 : ℝ) ^ (ε * N) *
        ∑ i ∈ Finset.range (2 ^ N), lpNorm (f i : E → ℂ) p volume ^ 2 := by
  let n := glyzFixedDepth n₀ q N
  let M := N / q + 1
  let D := C * (2 : ℝ) ^ (ε / 2 * q)
  have hn0 : n 0 ≤ N := glyzFixedDepth_le n₀ q N 0
  have hsum := lpNorm_sum_le (s := Finset.range (2 ^ n 0))
    (fun i _ => (glyzDyadicBlock f N (n 0) i).memLp p volume)
    (show (1 : ℝ≥0∞) ≤ p by exact_mod_cast hp)
  have hfun : (∑ i ∈ Finset.range (2 ^ n 0),
      ((glyzDyadicBlock f N (n 0) i : SchwartzMap E ℂ) : E → ℂ)) =
      ((∑ i ∈ Finset.range (2 ^ N), f i : SchwartzMap E ℂ) : E → ℂ) := by
    ext x
    have h := congrArg (fun F : SchwartzMap E ℂ => F x)
      (glyz_sum_dyadic_blocks f N (n 0) hn0)
    simpa only [sum_apply, Finset.sum_apply] using h
  rw [hfun] at hsum
  have hinit : lpNorm ((∑ i ∈ Finset.range (2 ^ N), f i : SchwartzMap E ℂ) : E → ℂ)
      p volume ^ 2 ≤ (2 : ℝ) ^ n 0 * glyzCurveScaleEnergy f N (n 0) p := by
    calc
      _ ≤ (∑ i ∈ Finset.range (2 ^ n 0),
        lpNorm ((glyzDyadicBlock f N (n 0) i : SchwartzMap E ℂ) : E → ℂ) p volume) ^ 2 :=
          pow_le_pow_left₀ lpNorm_nonneg hsum 2
      _ ≤ ((Finset.range (2 ^ n 0)).card : ℝ) *
        ∑ i ∈ Finset.range (2 ^ n 0),
          lpNorm ((glyzDyadicBlock f N (n 0) i : SchwartzMap E ℂ) : E → ℂ) p volume ^ 2 := sq_sum_le_card_mul_sum_sq
      _ = _ := by simp [glyzCurveScaleEnergy]
  have hit := glyzCurveScaleEnergy_iterate f N M n p (fun _ => D)
    (fun j _ => glyzFixedDepth_mono n₀ q N j) (fun _ _ => by dsimp [D]; positivity) hstep
  rw [show n M = N from glyzFixedDepth_finest n₀ q N hq, glyzCurveScaleEnergy_finest] at hit
  simp only [Finset.prod_const, Finset.card_range] at hit
  have he : 0 ≤ ∑ i ∈ Finset.range (2 ^ N), lpNorm (f i : E → ℂ) p volume ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc
    _ ≤ (2 : ℝ) ^ n 0 * glyzCurveScaleEnergy f N (n 0) p := hinit
    _ ≤ (2 : ℝ) ^ n 0 * (D ^ M * ∑ i ∈ Finset.range (2 ^ N), lpNorm (f i : E → ℂ) p volume ^ 2) :=
      mul_le_mul_of_nonneg_left hit (by positivity)
    _ = ((2 : ℝ) ^ min N n₀ * D ^ M) *
        ∑ i ∈ Finset.range (2 ^ N), lpNorm (f i : E → ℂ) p volume ^ 2 := by
      rw [show n 0 = min N n₀ from glyzFixedDepth_initial n₀ q N]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (glyz_fixed_step_coefficient_le n₀ q N hq hC hε habsorb) he

end PlanarNikodym
