import PlanarNikodym.Analysis.Fourier.GlyzRelativeKernelIteration

/-! Epsilon closure relative to an already decoupled family. The main
loss is proportional to the new depths, not to the entire final depth. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators ContDiff
namespace PlanarNikodym

set_option maxHeartbeats 1000000 in
theorem exists_glyz_actual_kernel_relative_epsilon_iteration {X : Type}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    (k : ℕ) (hk : 0 < k) {p σ ε : ℝ}
    (hp : 1 ≤ p) (hσ : 0 ≤ σ) (hε : 0 < ε) :
    ∃ ζ η : ℝ, 0 < ζ ∧ 0 < η ∧
    ∀ (c : ℕ) (C E Q : ℝ), 1 ≤ C → 0 ≤ E → 0 ≤ Q →
    ∃ K : ℝ, 0 < K ∧ ∀ N A F : ℕ,
    A ≤ F → F ≤ N →
    glyzVariableTerminalDepth k N (⌈ζ * N⌉₊ + c) ≤ F →
    F ≤ glyzVariableFinalDepth k N →
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
        ENNReal.ofReal (E * (2 : ℝ) ^ (-(Q + (σ + ε)) * N)) *
          (∫⁻ y, ‖glyzDyadicInput d i g y‖ₑ) ^ p) →
    glyzDyadicKernelEnergy μ H g A p ≤
      ENNReal.ofReal (K * (2 : ℝ) ^ (σ * ((F - A : ℕ) : ℝ) + ε * N)) *
        glyzDyadicKernelEnergy μ H g F p +
      ENNReal.ofReal (K * (2 : ℝ) ^ (-Q * N)) * (∫⁻ y, ‖g y‖ₑ) ^ p := by
  obtain ⟨ζ, η, hζ, hη, hbudget⟩ := exists_glyz_relative_exponent_budget k hk hp hσ hε
  obtain ⟨M, hM⟩ := exists_glyz_variable_offset_layers k hk hζ
  refine ⟨ζ, η, hζ, hη, fun c C E Q hC hE _hQ => ?_⟩
  let B : ℝ := (2 * k + 3 * c + 5) * (p - 1)
  let K₀ : ℝ := C ^ M * (2 : ℝ) ^ B
  let K : ℝ := K₀ * (1 + (M : ℝ) * E)
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hK₀ : 0 < K₀ := mul_pos (pow_pos hC0 _) (by positivity)
  have hK : 0 < K := mul_pos hK₀ (by positivity)
  have hK₀K : K₀ ≤ K := by
    have hm : 0 ≤ (M : ℝ) * E := mul_nonneg (Nat.cast_nonneg M) hE
    dsimp [K]
    nlinarith
  have hKE : K₀ * M * E ≤ K := by dsimp [K]; nlinarith
  refine ⟨K, hK, fun N A F hAF hFN hTF hFF μ H g hH hc hg hs hstep => ?_⟩
  let Z := ⌈ζ * N⌉₊ + c
  let T := glyzVariableTerminalDepth k N Z
  let a := max A (min T (2 * Z + 2 * k))
  let t := max A T
  let b : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (σ + η))
  let e : ℝ≥0∞ := ENNReal.ofReal (E * (2 : ℝ) ^ (-(Q + (σ + ε)) * N))
  let U : ℝ≥0∞ := ((2 ^ (a - A) : ℕ) : ℝ≥0∞) ^ (p - 1) *
    ((ENNReal.ofReal C) ^ M * b ^ (t - a))
  let v : ℝ≥0∞ := ((2 ^ (F - t) : ℕ) : ℝ≥0∞) ^ (p - 1)
  have hAa : A ≤ a := le_max_left _ _
  have hat : a ≤ t := max_le_max_left _ (min_le_left _ _)
  have htF : t ≤ F := max_le hAF hTF
  have hTN : T ≤ N := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hb : 1 ≤ b := by
    simpa [b] using ENNReal.ofReal_le_ofReal
      (Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) (add_nonneg hσ hη.le))
  have hC' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal C := by
    exact_mod_cast (ENNReal.ofReal_le_ofReal hC)
  have hstep' : ∀ d m : ℕ, d < m → k * (m - d) + Z ≤ d → k * m + Z ≤ N →
      ∀ i < 2 ^ d, (∫⁻ x, ‖glyzDyadicKernelPiece H g d i x‖ₑ ^ p ∂μ) ≤
        (ENNReal.ofReal C * b ^ (m - d)) * glyzDyadicBlock
          (fun j => ∫⁻ x, ‖glyzDyadicKernelPiece H g m j x‖ₑ ^ p ∂μ) m d i +
        e * (∫⁻ y, ‖glyzDyadicInput d i g y‖ₑ) ^ p := by
    intro d m hdm hd hm i hi
    convert hstep d m hdm hd hm i hi using 1
    rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ (2 : ℝ) ^ (σ + η)),
      ← ENNReal.ofReal_mul hC0.le,
      ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  have hit₀ := glyz_actual_kernel_relative_stopped_iteration μ hH hc hg hs
    k N Z M A F hAF hTF (hM N c T hTN) hp (ENNReal.ofReal C) b e hC' hb hstep'
  have hit : glyzDyadicKernelEnergy μ H g A p ≤
      (U * v) * glyzDyadicKernelEnergy μ H g F p +
        (U * ((M : ℝ≥0∞) * e)) * (∫⁻ y, ‖g y‖ₑ) ^ p := by
    simpa only [U, v, T, a, t, mul_assoc, mul_left_comm, mul_comm] using hit₀
  have hv : 1 ≤ v := by
    dsimp [v]
    have hbase : (1 : ℝ≥0∞) ≤ ((2 ^ (F - t) : ℕ) : ℝ≥0∞) := by
      exact_mod_cast (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2) : 1 ≤ 2 ^ (F - t))
    simpa using ENNReal.rpow_le_rpow hbase (sub_nonneg.mpr hp)
  have hUv : U ≤ U * v := le_mul_of_one_le_right' hv
  have hcoef : U * v ≤ ENNReal.ofReal
      (K₀ * (2 : ℝ) ^ (σ * ((F - A : ℕ) : ℝ) + ε * N)) := by
    have heq := glyz_variable_iteration_coefficient (a - A) (t - A) (F - A) M
      hC0.le p (σ + η)
    have hta : t - A - (a - A) = t - a := by omega
    have hFt : F - A - (t - A) = F - t := by omega
    rw [hta, hFt] at heq
    change _ ≤ _
    dsimp [U, v, b]
    rw [heq]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ C ^ M * (2 : ℝ) ^
          (σ * ((F - A : ℕ) : ℝ) + ε * N + B) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hC0.le _)
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        exact hbudget N c A F hAF hTF hFF
      _ = _ := by rw [Real.rpow_add (by norm_num)]; dsimp [K₀]; ring
  have hmain : U * v ≤ ENNReal.ofReal
      (K * (2 : ℝ) ^ (σ * ((F - A : ℕ) : ℝ) + ε * N)) :=
    hcoef.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hK₀K (by positivity)))
  have hcoarse : U * v ≤ ENNReal.ofReal (K₀ * (2 : ℝ) ^ ((σ + ε) * N)) := by
    apply hcoef.trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hK₀.le
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hd : ((F - A : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.sub_le F A).trans hFN
    nlinarith
  have herr : U * ((M : ℝ≥0∞) * e) ≤ ENNReal.ofReal (K * (2 : ℝ) ^ (-Q * N)) := by
    calc
      _ ≤ (U * v) * ((M : ℝ≥0∞) * e) := mul_le_mul_left hUv _
      _ ≤ ENNReal.ofReal (K₀ * (2 : ℝ) ^ ((σ + ε) * N)) * ((M : ℝ≥0∞) * e) :=
        mul_le_mul_left hcoarse _
      _ = ENNReal.ofReal ((K₀ * M * E) * (2 : ℝ) ^ (-Q * N)) := by
        have hexp : (2 : ℝ) ^ ((σ + ε) * N) * (2 : ℝ) ^ (-(Q + (σ + ε)) * N) =
            (2 : ℝ) ^ (-Q * N) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1
          ring
        rw [show (M : ℝ≥0∞) = ENNReal.ofReal (M : ℝ) by simp]
        dsimp [e]
        rw [← ENNReal.ofReal_mul (Nat.cast_nonneg M), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        calc
          _ = (K₀ * M * E) *
              ((2 : ℝ) ^ ((σ + ε) * N) * (2 : ℝ) ^ (-(Q + (σ + ε)) * N)) := by ring
          _ = _ := by rw [hexp]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hKE (by positivity))
  exact hit.trans (add_le_add (mul_le_mul_left hmain _) (mul_le_mul_left herr _))

end PlanarNikodym
