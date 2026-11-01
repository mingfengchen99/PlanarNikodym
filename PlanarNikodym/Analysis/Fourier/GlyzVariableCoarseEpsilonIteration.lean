import PlanarNikodym.Analysis.Fourier.GlyzVariableTargetIteration

/-! The same genuine finite iteration may stop a fixed number of
generations before the usual final depth. A larger fixed Fourier
offset absorbs this change without changing the frequency exponent. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators ContDiff
namespace PlanarNikodym

set_option maxHeartbeats 800000 in
/-- A fixed number of genuine parent estimates gives the sharp main
exponent and an arbitrary negative frequency power. All constants are
chosen before the actual frequency, kernel, and input. -/
theorem exists_glyz_actual_kernel_coarse_epsilon_iteration {X : Type}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    (k : ℕ) (hk : 0 < k) (s : ℕ) {p σ ε : ℝ}
    (hp : 1 ≤ p) (hσ : 0 ≤ σ) (hε : 0 < ε) :
    ∃ ζ η : ℝ, 0 < ζ ∧ 0 < η ∧
    ∀ (c : ℕ) (C E Q : ℝ), k * (s + 1) ≤ c → 1 ≤ C → 0 ≤ E → 0 ≤ Q →
    ∃ K : ℝ, 0 < K ∧
    ∀ (N : ℕ) (Λ : ℝ), (2 : ℝ) ^ N ≤ Λ → Λ ≤ (2 : ℝ) ^ (N + 1) →
    ∀ (μ : Measure X) (H : X × Plane → ℂ) (g : Plane → ℂ),
    ContDiff ℝ ∞ H → HasCompactSupport H → Integrable g →
    Function.support g ⊆ {y | y.1 ∈ Ico (0 : ℝ) 1} →
    (∀ d m : ℕ, d < m →
      k * (m - d) + (⌈ζ * N⌉₊ + c) ≤ d →
      k * m + (⌈ζ * N⌉₊ + c) ≤ N → ∀ i < 2 ^ d,
      (∫⁻ x, ‖glyzDyadicKernelPiece H g d i x‖ₑ ^ p ∂μ) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^ ((σ + η) * ((m - d : ℕ) : ℝ))) *
          glyzDyadicBlock
            (fun j => ∫⁻ x, ‖glyzDyadicKernelPiece H g m j x‖ₑ ^ p ∂μ) m d i +
        ENNReal.ofReal (E * (2 : ℝ) ^ (-(Q + (σ / k + ε)) * N)) *
          (∫⁻ y, ‖glyzDyadicInput d i g y‖ₑ) ^ p) →
    (∫⁻ x, ‖∫ y, g y * H (x, y)‖ₑ ^ p ∂μ) ≤
      ENNReal.ofReal (K * Λ ^ (σ / k + ε)) *
        glyzDyadicKernelEnergy μ H g (glyzVariableFinalDepth k N - s) p +
      ENNReal.ofReal (K * Λ ^ (-Q)) * (∫⁻ y, ‖g y‖ₑ) ^ p := by
  obtain ⟨ζ, η, hζ, hη, hbudget⟩ :=
    exists_glyz_variable_total_exponent_budget k hk hp hσ hε
  obtain ⟨M, hM⟩ := exists_glyz_variable_offset_layers k hk hζ
  refine ⟨ζ, η, hζ, hη, fun c C E Q hcs hC hE hQ => ?_⟩
  let B : ℝ := (2 * k + 3 * c + 5) * (p - 1)
  let a : ℝ := σ / k + ε
  let K₀ : ℝ := C ^ M * (2 : ℝ) ^ B
  let K : ℝ := K₀ * (1 + (M : ℝ) * E * (2 : ℝ) ^ Q)
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hK₀ : 0 < K₀ := mul_pos (pow_pos hC0 _) (by positivity)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hK : 0 < K := mul_pos hK₀ (by positivity)
  have hK₀K : K₀ ≤ K := by
    dsimp [K]
    exact le_mul_of_one_le_right hK₀.le
      (by have : 0 ≤ (M : ℝ) * E * (2 : ℝ) ^ Q := by positivity
          linarith)
  have hKE : K₀ * M * E * (2 : ℝ) ^ Q ≤ K := by
    dsimp [K]
    nlinarith
  refine ⟨K, hK, fun N Λ hΛ hΛ' μ H g hH hc hg hs hstep => ?_⟩
  have hΛ0 : 0 < Λ := lt_of_lt_of_le (by positivity) hΛ
  let Z := ⌈ζ * N⌉₊ + c
  let T := glyzVariableTerminalDepth k N Z
  let d := min T (2 * Z + 2 * k)
  let F := glyzVariableFinalDepth k N - s
  let b : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (σ + η))
  let e : ℝ≥0∞ := ENNReal.ofReal (E * (2 : ℝ) ^ (-(Q + a) * N))
  let A : ℝ≥0∞ := ((2 ^ d : ℕ) : ℝ≥0∞) ^ (p - 1) *
    ((ENNReal.ofReal C) ^ M * b ^ (T - d))
  let t : ℝ≥0∞ := ((2 ^ (F - T) : ℕ) : ℝ≥0∞) ^ (p - 1)
  have hTN : T ≤ N := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hstop := hM N c T hTN
  have hTF : T ≤ F := glyz_variable_terminal_le_coarse k N Z s hk
    (by dsimp only [Z]; nlinarith)
  have hgap : F - T ≤ glyzVariableFinalDepth k N - T :=
    Nat.sub_le_sub_right (Nat.sub_le _ _) T
  have hbudget' :
      (d : ℝ) * (p - 1) + (σ + η) * ((T - d : ℕ) : ℝ) +
        ((F - T : ℕ) : ℝ) * (p - 1) ≤ a * N + B := by
    calc
      _ ≤ (d : ℝ) * (p - 1) + (σ + η) * ((T - d : ℕ) : ℝ) +
          ((glyzVariableFinalDepth k N - T : ℕ) : ℝ) * (p - 1) := by
        gcongr
      _ ≤ _ := hbudget N c
  have hb : 1 ≤ b := by
    simpa [b] using ENNReal.ofReal_le_ofReal
      (Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) (add_nonneg hσ hη.le))
  have hC' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal C := by
    exact_mod_cast (ENNReal.ofReal_le_ofReal hC)
  have hstep' : ∀ d' m : ℕ, d' < m → k * (m - d') + Z ≤ d' →
      k * m + Z ≤ N → ∀ i < 2 ^ d',
      (∫⁻ x, ‖glyzDyadicKernelPiece H g d' i x‖ₑ ^ p ∂μ) ≤
        (ENNReal.ofReal C * b ^ (m - d')) *
          glyzDyadicBlock
            (fun j => ∫⁻ x, ‖glyzDyadicKernelPiece H g m j x‖ₑ ^ p ∂μ) m d' i +
        e * (∫⁻ y, ‖glyzDyadicInput d' i g y‖ₑ) ^ p := by
    intro d' m hdm hd hm i hi
    convert hstep d' m hdm hd hm i hi using 1
    rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ (2 : ℝ) ^ (σ + η)),
      ← ENNReal.ofReal_mul hC0.le,
      ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  have hit₀ := glyz_actual_kernel_stopped_iteration_to μ hH hc hg hs k N Z M F hTF hstop
    hp (ENNReal.ofReal C) b e hC' hb hstep'
  have hit : (∫⁻ x, ‖∫ y, g y * H (x, y)‖ₑ ^ p ∂μ) ≤
    (A * t) * glyzDyadicKernelEnergy μ H g F p +
      (A * ((M : ℝ≥0∞) * e)) * (∫⁻ y, ‖g y‖ₑ) ^ p := by
    simpa only [A, t, F, T, d, mul_assoc, mul_left_comm, mul_comm] using hit₀
  have ht : 1 ≤ t := by
    dsimp [t]
    have hbase : (1 : ℝ≥0∞) ≤ ((2 ^ (F - T) : ℕ) : ℝ≥0∞) := by
      exact_mod_cast (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2) : 1 ≤ 2 ^ (F - T))
    simpa using ENNReal.rpow_le_rpow hbase (sub_nonneg.mpr hp)
  have hAt : A ≤ A * t := le_mul_of_one_le_right' ht
  have hcoef : A * t ≤ ENNReal.ofReal (K₀ * (2 : ℝ) ^ (a * N)) := by
    dsimp [A, t, b]
    rw [glyz_variable_iteration_coefficient d T F M hC0.le p (σ + η)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ C ^ M * (2 : ℝ) ^ (a * N + B) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hC0.le _)
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        exact hbudget'
      _ = _ := by rw [Real.rpow_add (by norm_num)]; dsimp [K₀]; ring
  have hmain : A * t ≤ ENNReal.ofReal (K * Λ ^ a) := by
    apply hcoef.trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul hK₀K (glyz_variable_shell_nonneg_power N hΛ ha)
      (by positivity) hK.le
  have herr : A * ((M : ℝ≥0∞) * e) ≤ ENNReal.ofReal (K * Λ ^ (-Q)) := by
    calc
      _ ≤ (A * t) * ((M : ℝ≥0∞) * e) := mul_le_mul_left hAt _
      _ ≤ ENNReal.ofReal (K₀ * (2 : ℝ) ^ (a * N)) * ((M : ℝ≥0∞) * e) :=
        mul_le_mul_left hcoef _
      _ = ENNReal.ofReal ((K₀ * M * E) * (2 : ℝ) ^ (-Q * N)) := by
        have hexp : (2 : ℝ) ^ (a * N) * (2 : ℝ) ^ (-(Q + a) * N) =
            (2 : ℝ) ^ (-Q * N) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1
          ring
        rw [show (M : ℝ≥0∞) = ENNReal.ofReal (M : ℝ) by simp]
        dsimp [e]
        rw [← ENNReal.ofReal_mul (Nat.cast_nonneg M),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        calc
          _ = (K₀ * M * E) *
              ((2 : ℝ) ^ (a * N) * (2 : ℝ) ^ (-(Q + a) * N)) := by ring
          _ = _ := by rw [hexp]
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        calc
          _ ≤ (K₀ * M * E) * ((2 : ℝ) ^ Q * Λ ^ (-Q)) :=
            mul_le_mul_of_nonneg_left
              (glyz_variable_shell_decay N hΛ0 hΛ' hQ)
              (by positivity)
          _ ≤ K * Λ ^ (-Q) := by
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right hKE (by positivity)
  exact hit.trans (add_le_add
    (mul_le_mul_left hmain _) (mul_le_mul_left herr _))

end PlanarNikodym
