import PlanarNikodym.Analysis.Fourier.GlyzParabolicErrorReduction
import PlanarNikodym.Analysis.Fourier.GlyzVariableNumericalBudget

/-! The explicit parabolic chart error has arbitrarily rapid decay.
The differentiation order is chosen before all chart constants, so
the choice does not depend circularly on constants produced by that
same differentiation order. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace PlanarNikodym

set_option maxHeartbeats 800000 in
/-- Arbitrary negative powers for the actual scalar error coefficient.
Both the parent depth and the relative refinement depth may vary up to
the original frequency depth. -/
theorem exists_glyz_parabolic_error_decay_order (k W : ℕ)
    (hW : Module.finrank ℝ (GlyzConeSpace k) < W)
    (p : ℝ≥0) (hp : 0 < p) (η : ℝ)
    (hs : 0 ≤ (p : ℝ) - glyzCriticalExponent k / 2 - 1 + η)
    {ζ : ℝ} (hζ : 0 < ζ) (Q : ℝ) :
    ∃ M : ℕ, ∀ C D L : ℝ, 0 ≤ C → 0 ≤ D → 0 ≤ L →
    ∃ E : ℝ, 0 ≤ E ∧ ∀ N d q : ℕ, d ≤ N → q ≤ N →
      ∀ α : ℝ, |α| ≤ (2 : ℝ) ^ (N + 1) →
      glyzParabolicErrorCoefficient k W M p η C D L
        (glyzDyadicScale d) α q ((2 : ℝ) ^ (ζ * N)) ≤
          ENNReal.ofReal (E * (2 : ℝ) ^ (-Q * N)) := by
  let a := (volume : Measure (GlyzConeSpace k)).integrablePower
  let dim := Module.finrank ℝ (GlyzConeSpace k)
  let s := (p : ℝ) - glyzCriticalExponent k / 2 - 1 + η
  obtain ⟨M, hM⟩ := exists_glyz_variable_tail_power_order a hζ hp
    (s + (k * dim : ℕ)) Q
  refine ⟨M, fun C D L hC hD hL => ?_⟩
  let b : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (p : ℝ)
  let w := ∫⁻ x : GlyzConeSpace k, ENNReal.ofReal (glyzNormWeight W x)
  let u := volume (closedBall (0 : GlyzConeSpace k) 1)
  let K : ℝ≥0∞ := b * (ENNReal.ofReal C * b * w + u)
  have hb : b ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg p.coe_nonneg (by norm_num)
  have hw : w ≠ ⊤ := glyzNormWeight_lintegral_ne_top hW
  have hu : u ≠ ⊤ := measure_closedBall_lt_top.ne
  have hK : K ≠ ⊤ := ENNReal.mul_ne_top hb
    (ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb) hw, hu⟩)
  let E := K.toReal * D ^ (p : ℝ) * (L + 1) ^ dim *
    (2 : ℝ) ^ ((2 * a : ℕ) * (p : ℝ))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨E, hE, fun N d q hd hq α hα => ?_⟩
  let t := (1 + |α|) ^ a * ((2 : ℝ) ^ (ζ * N)) ^ (-(M : ℝ))
  let v := (((glyzDyadicScale d ^ k)⁻¹ * L + 1) ^ dim)
  let P := ENNReal.ofReal ((2 : ℝ) ^ (s * N))
  have hP : (1 : ℝ≥0∞) ≤ P := by
    simpa [P] using ENNReal.ofReal_le_ofReal
      (Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2)
        (mul_nonneg hs (Nat.cast_nonneg N)))
  have hqP : ENNReal.ofReal ((2 : ℝ) ^ (s * q)) ≤ P := by
    apply ENNReal.ofReal_le_ofReal
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hq) hs)
  have hpref : b *
      (ENNReal.ofReal (C * (2 : ℝ) ^ (s * q)) * b * w + u) ≤ K * P := by
    rw [ENNReal.ofReal_mul hC]
    calc
      _ ≤ b * ((ENNReal.ofReal C * P) * b * w + u * P) := by
        apply mul_le_mul_right
        apply add_le_add
        · exact mul_le_mul_left (mul_le_mul_left
            (mul_le_mul_right hqP (ENNReal.ofReal C)) b) w
        · exact le_mul_of_one_le_right' hP
      _ = _ := by dsimp [K]; ring
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have htail : D * (1 + |α|) ^ a * (((2 : ℝ) ^ (ζ * N))⁻¹) ^ M = D * t := by
    dsimp [t]
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (ζ * N)),
      Real.rpow_natCast, inv_pow]
    ring
  have htailpow : ENNReal.ofReal (D * t) ^ (p : ℝ) =
      ENNReal.ofReal (D ^ (p : ℝ) * t ^ (p : ℝ)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hD ht0) p.coe_nonneg,
      Real.mul_rpow hD ht0]
  have hvol := glyz_variable_output_volume_le k d N dim hL hd
  have htailbound := hM N α hα
  change b * (ENNReal.ofReal (C * (2 : ℝ) ^ (s * q)) * b * w + u) *
    ENNReal.ofReal (D * (1 + |α|) ^ a * (((2 : ℝ) ^ (ζ * N))⁻¹) ^ M) ^ (p : ℝ) *
    ENNReal.ofReal v ≤ _
  rw [htail, htailpow]
  calc
    _ ≤ (K * P) * ENNReal.ofReal (D ^ (p : ℝ) * t ^ (p : ℝ)) *
        ENNReal.ofReal ((L + 1) ^ dim * (2 : ℝ) ^ ((k * dim : ℕ) * (N : ℝ))) := by
      exact mul_le_mul
        (mul_le_mul_left hpref _) (ENNReal.ofReal_le_ofReal hvol) zero_le zero_le
    _ = ENNReal.ofReal (K.toReal * D ^ (p : ℝ) * (L + 1) ^ dim *
        ((2 : ℝ) ^ ((s + (k * dim : ℕ)) * N) * t ^ (p : ℝ))) := by
      nth_rw 1 [← ENNReal.ofReal_toReal hK]
      dsimp only [P]
      rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have hexp : (2 : ℝ) ^ ((s + (k * dim : ℕ)) * N) =
          (2 : ℝ) ^ (s * N) * (2 : ℝ) ^ ((k * dim : ℕ) * (N : ℝ)) := by
        convert Real.rpow_add (by norm_num : (0 : ℝ) < 2)
          (s * N) ((k * dim : ℕ) * (N : ℝ)) using 1
        congr 1
        ring
      rw [hexp]
      ring
    _ ≤ ENNReal.ofReal (K.toReal * D ^ (p : ℝ) * (L + 1) ^ dim *
        ((2 : ℝ) ^ ((2 * a : ℕ) * (p : ℝ)) * (2 : ℝ) ^ (-Q * N))) :=
      ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left htailbound (by positivity))
    _ = _ := by dsimp [E]; congr 1; ring

end PlanarNikodym
