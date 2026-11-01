import PlanarNikodym.Analysis.Fourier.GlyzVariableNumericalBudget

/-! Composition retains a prescribed arbitrary decay order even when
an earlier main estimate amplifies the later error. -/
noncomputable section
open scoped ENNReal
namespace PlanarNikodym

theorem glyz_power_error_compose {X Y Z E : ℝ≥0∞} {C D r a b Q : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hr : 1 ≤ r)
    (hx : X ≤ ENNReal.ofReal (C * r ^ a) * Y + ENNReal.ofReal (C * r ^ (-Q)) * E)
    (hy : Y ≤ ENNReal.ofReal (D * r ^ b) * Z +
      ENNReal.ofReal (D * r ^ (-(Q + |a|))) * E) :
    X ≤ ENNReal.ofReal (C * (D + 1) * r ^ (a + b)) * Z +
      ENNReal.ofReal (C * (D + 1) * r ^ (-Q)) * E := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hmain : ENNReal.ofReal (C * r ^ a) * ENNReal.ofReal (D * r ^ b) ≤
      ENNReal.ofReal (C * (D + 1) * r ^ (a + b)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.rpow_add hr0]
    calc
      C * r ^ a * (D * r ^ b) = (C * D) * (r ^ a * r ^ b) := by ring
      _ ≤ (C * (D + 1)) * (r ^ a * r ^ b) :=
        mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  have herr : ENNReal.ofReal (C * r ^ a) * ENNReal.ofReal (D * r ^ (-(Q + |a|))) +
      ENNReal.ofReal (C * r ^ (-Q)) ≤ ENNReal.ofReal (C * (D + 1) * r ^ (-Q)) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hp : r ^ a * r ^ (-(Q + |a|)) ≤ r ^ (-Q) := by
      rw [← Real.rpow_add hr0]
      apply Real.rpow_le_rpow_of_exponent_le hr
      linarith [le_abs_self a]
    have hm := mul_le_mul_of_nonneg_left hp (mul_nonneg hC hD)
    calc
      C * r ^ a * (D * r ^ (-(Q + |a|))) + C * r ^ (-Q) =
          (C * D) * (r ^ a * r ^ (-(Q + |a|))) + C * r ^ (-Q) := by ring
      _ ≤ (C * D) * r ^ (-Q) + C * r ^ (-Q) := add_le_add hm le_rfl
      _ = _ := by ring
  calc
    X ≤ ENNReal.ofReal (C * r ^ a) *
        (ENNReal.ofReal (D * r ^ b) * Z + ENNReal.ofReal (D * r ^ (-(Q + |a|))) * E) +
        ENNReal.ofReal (C * r ^ (-Q)) * E := hx.trans (by gcongr)
    _ = (ENNReal.ofReal (C * r ^ a) * ENNReal.ofReal (D * r ^ b)) * Z +
        (ENNReal.ofReal (C * r ^ a) * ENNReal.ofReal (D * r ^ (-(Q + |a|))) +
          ENNReal.ofReal (C * r ^ (-Q))) * E := by ring
    _ ≤ _ := add_le_add (mul_le_mul_left hmain _) (mul_le_mul_left herr _)

end PlanarNikodym
