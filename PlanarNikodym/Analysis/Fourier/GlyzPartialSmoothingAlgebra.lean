import PlanarNikodym.Analysis.Fourier.GlyzPowerErrorComposition

/-! The frequency normalization and arbitrary L1 remainder in the
actual partial-extension smoothing assembly. -/
noncomputable section
namespace PlanarNikodym

theorem glyz_partial_smoothing_combine {c C D V r x y m n l α b Q : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hD : 0 ≤ D) (hV : 0 ≤ V) (hr : 0 < r)
    (hn : 0 ≤ n) (hl : 0 ≤ l)
    (hx : x ≤ C * (c * r) ^ α * y + C * r ^ 2 * (c * r) ^ (-(Q + 2)) * m)
    (hy : y ≤ D * r ^ b * n) (hm : m ≤ V * l) :
    x ≤ (C * (c ^ α * D + c ^ (-(Q + 2)) * V) + 1) * r ^ (α + b) * n +
      (C * (c ^ α * D + c ^ (-(Q + 2)) * V) + 1) * r ^ (-Q) * l := by
  let A := C * c ^ α * D
  let B := C * c ^ (-(Q + 2)) * V
  let K := C * (c ^ α * D + c ^ (-(Q + 2)) * V) + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hAK : A ≤ K := by dsimp [A, B, K] at *; nlinarith
  have hBK : B ≤ K := by dsimp [A, B, K] at *; nlinarith
  have he : r ^ 2 * r ^ (-(Q + 2)) = r ^ (-Q) := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_add hr]
    norm_num
  calc
    x ≤ C * (c * r) ^ α * (D * r ^ b * n) +
        C * r ^ 2 * (c * r) ^ (-(Q + 2)) * (V * l) := by
      exact hx.trans (add_le_add (mul_le_mul_of_nonneg_left hy (by positivity))
        (mul_le_mul_of_nonneg_left hm (by positivity)))
    _ = A * r ^ (α + b) * n + B * r ^ (-Q) * l := by
      rw [Real.mul_rpow hc.le hr.le, Real.mul_rpow hc.le hr.le, Real.rpow_add hr]
      dsimp [A, B]
      calc
        _ = C * c ^ α * D * (r ^ α * r ^ b) * n +
            C * c ^ (-(Q + 2)) * V * (r ^ 2 * r ^ (-(Q + 2))) * l := by ring
        _ = _ := by rw [he]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAK (by positivity)) hn)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBK (by positivity)) hl)

end PlanarNikodym
