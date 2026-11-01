import PlanarNikodym.Analysis.Fourier.GlyzParabolicErrorBudget

/-! Uniform constants for the finite atlas of actual parabolic charts.
The Fourier order is chosen before the atlas and all of its constants.
The atlas contributes only fixed finite main and error constants. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace PlanarNikodym

theorem glyzParabolicPowerCoefficient_scale (k : ℕ) (p : ℝ≥0)
    (η C Cg : ℝ) (hC : 0 ≤ C) (q : ℕ) :
    glyzParabolicPowerCoefficient k p η C Cg q =
      glyzParabolicPowerCoefficient k p η C Cg 0 *
        ENNReal.ofReal ((2 : ℝ) ^
          (((p : ℝ) - glyzCriticalExponent k / 2 - 1 + η) * q)) := by
  simp only [glyzParabolicPowerCoefficient, Nat.cast_zero, mul_zero,
    Real.rpow_zero, mul_one, ENNReal.ofReal_mul hC]
  ring

/-- One Fourier order works for every subsequently constructed finite
atlas. The weights include its Jacobians and finite-cover factors. -/
theorem exists_glyz_finite_parabolic_budget (k W : ℕ)
    (hW : Module.finrank ℝ (GlyzConeSpace k) < W)
    (p : ℝ≥0) (hp : 0 < p) (η : ℝ)
    (hs : 0 ≤ (p : ℝ) - glyzCriticalExponent k / 2 - 1 + η)
    {ζ : ℝ} (hζ : 0 < ζ) (Q : ℝ) :
    ∃ M : ℕ, ∀ (m : ℕ) (u v : Fin m → ℝ≥0∞)
      (C D L Cg : Fin m → ℝ),
      (∀ i, u i ≠ ⊤) → (∀ i, v i ≠ ⊤) →
      (∀ i, 0 ≤ C i) → (∀ i, 0 ≤ D i) → (∀ i, 0 ≤ L i) →
    ∃ C₀ E₀ : ℝ, 1 ≤ C₀ ∧ 0 ≤ E₀ ∧ ∀ N d q : ℕ, d ≤ N → q ≤ N →
      ∀ α : ℝ, |α| ≤ (2 : ℝ) ^ (N + 1) →
      (∑ i, u i * glyzParabolicPowerCoefficient k p η (C i) (Cg i) q) ≤
        ENNReal.ofReal (C₀ * (2 : ℝ) ^
          (((p : ℝ) - glyzCriticalExponent k / 2 - 1 + η) * q)) ∧
      (∑ i, v i * glyzParabolicErrorCoefficient k W M p η (C i) (D i) (L i)
        (glyzDyadicScale d) α q ((2 : ℝ) ^ (ζ * N))) ≤
        ENNReal.ofReal (E₀ * (2 : ℝ) ^ (-Q * N)) := by
  classical
  obtain ⟨M, hM⟩ := exists_glyz_parabolic_error_decay_order k W hW p hp η hs hζ Q
  refine ⟨M, fun m u v C D L Cg hu hv hC hD hL => ?_⟩
  have hi := fun i => hM (C i) (D i) (L i) (hC i) (hD i) (hL i)
  choose E hE hbound using hi
  let A : ℝ≥0∞ := ∑ i, u i * glyzParabolicPowerCoefficient k p η (C i) (Cg i) 0
  let B : ℝ≥0∞ := ∑ i, v i * ENNReal.ofReal (E i)
  have hA : A ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ =>
    ENNReal.mul_ne_top (hu i) (glyzParabolicPowerCoefficient_ne_top k p η (C i) (Cg i) 0)
  have hB : B ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ =>
    ENNReal.mul_ne_top (hv i) ENNReal.ofReal_ne_top
  let C₀ := A.toReal + 1
  have hC₀ : 1 ≤ C₀ := by dsimp [C₀]; linarith [ENNReal.toReal_nonneg (a := A)]
  have hAC : A ≤ ENNReal.ofReal C₀ := by
    calc
      _ = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hA).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by dsimp [C₀]; linarith)
  refine ⟨C₀, B.toReal, hC₀, ENNReal.toReal_nonneg, fun N d q hd hq α hα => ⟨?_, ?_⟩⟩
  · calc
      _ = A * ENNReal.ofReal ((2 : ℝ) ^
          (((p : ℝ) - glyzCriticalExponent k / 2 - 1 + η) * q)) := by
        simp_rw [glyzParabolicPowerCoefficient_scale k p η _ _ (hC _) q]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_assoc]
      _ ≤ ENNReal.ofReal C₀ * ENNReal.ofReal ((2 : ℝ) ^
          (((p : ℝ) - glyzCriticalExponent k / 2 - 1 + η) * q)) :=
        mul_le_mul_left hAC _
      _ = _ := (ENNReal.ofReal_mul (zero_le_one.trans hC₀)).symm
  · calc
      _ ≤ ∑ i, v i * ENNReal.ofReal (E i * (2 : ℝ) ^ (-Q * N)) := by
        exact Finset.sum_le_sum fun i _ => mul_le_mul_right (hbound i N d q hd hq α hα) _
      _ = B * ENNReal.ofReal ((2 : ℝ) ^ (-Q * N)) := by
        simp_rw [ENNReal.ofReal_mul (hE _)]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_assoc]
      _ = _ := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hB]

end PlanarNikodym
