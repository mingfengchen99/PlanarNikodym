import PlanarNikodym.Analysis.Fourier.GlyzAffineBoxInterpolation
import PlanarNikodym.Analysis.Fourier.GlyzFiniteFamilyTransport
import PlanarNikodym.Analysis.Fourier.GlyzCriticalMomentDecoupling
import PlanarNikodym.Analysis.Fourier.GlyzEnlargedMomentDecoupling
import PlanarNikodym.Analysis.Fourier.GlyzPowerIntegralLp

/-! Actual critical and supercritical moment decoupling with the sharp
ℓp loss. The high-exponent conclusion uses constructed Fourier projections
and real operator interpolation; it has no decoupling assumption. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform ENNReal NNReal BigOperators
namespace PlanarNikodym

theorem glyz_enlarged_critical_decoupling_fin (m : ℕ) (hm : 0 < m)
    (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ f : Fin (2 ^ N) → SchwartzMap (GlyzSpace m) ℂ,
      (∀ i, Function.support (𝓕 (f i : GlyzSpace m → ℂ)) ⊆
        glyzFrequencyBox (glyzMomentFrequencyFrame m (glyzDyadicCenter N i)
          (glyzDyadicScale N) (glyzDyadicScale_pos N))
          ((EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m (glyzDyadicCenter N i))) R) →
      lpNorm ((∑ i, f i : SchwartzMap (GlyzSpace m) ℂ) : GlyzSpace m → ℂ)
          (glyzCriticalNNExponent m) volume ^ 2 ≤
        C * (2 : ℝ) ^ (ε * N) *
          ∑ i, lpNorm (f i : GlyzSpace m → ℂ) (glyzCriticalNNExponent m) volume ^ 2 := by
  obtain ⟨C, hC, h⟩ := glyz_enlarged_dyadic_decoupling_of_admissible_square_loss
    (one_le_glyzCriticalNNExponent hm) (glyz_critical_admissible_square_loss m hm hε) R
  refine ⟨C, hC, fun N f hf => ?_⟩
  have hs : GlyzDyadicEnlargedSupported m N R (glyzFinExtend f) := by
    intro i hi
    have hi' : i < 2 ^ N := Finset.mem_range.mp hi
    simpa only [glyzFinExtend, dif_pos hi'] using hf ⟨i, hi'⟩
  have hh := h N (glyzFinExtend f) hs
  have hsum : (fun x => ∑ i ∈ Finset.range (2 ^ N), glyzFinExtend f i x) =
      ((∑ i, f i : SchwartzMap (GlyzSpace m) ℂ) : GlyzSpace m → ℂ) := by
    ext x
    rw [← sum_apply, sum_glyzFinExtend]
  rw [hsum] at hh
  unfold glyzDyadicSquareEnergy at hh
  rw [sum_comp_glyzFinExtend f
    (fun v : SchwartzMap (GlyzSpace m) ℂ =>
      lpNorm (v : GlyzSpace m → ℂ) (glyzCriticalNNExponent m) volume ^ 2)] at hh
  exact hh

/-- The ℓp power-integral form, including the critical endpoint, with
one constant before the depth and Fourier-supported Schwartz family. -/
theorem glyz_supercritical_moment_power_decoupling (m : ℕ) (hm : 0 < m)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent m ≤ p)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (f : ℕ → SchwartzMap (GlyzSpace m) ℂ),
      GlyzDyadicEnlargedSupported m N R f →
      (∫⁻ x, ENNReal.ofReal (‖(∑ i ∈ Finset.range (2 ^ N), f i :
        SchwartzMap (GlyzSpace m) ℂ) x‖ ^ (p : ℝ))) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^
          (((p : ℝ) - glyzCriticalExponent m / 2 - 1 + ε) * N)) *
            ∑ i ∈ Finset.range (2 ^ N), ∫⁻ x, ENNReal.ofReal (‖f i x‖ ^ (p : ℝ)) := by
  let q := glyzCriticalNNExponent m
  have hq : 2 ≤ q := two_le_glyzCriticalNNExponent hm
  have hq0 : (0 : ℝ) < q := glyzCriticalExponent_pos hm
  have hqdef : (q : ℝ) = glyzCriticalExponent m := rfl
  have hα : 0 < 2 * ε / (q : ℝ) := by positivity
  by_cases heq : p = q
  · subst p
    obtain ⟨C, hC, hcrit⟩ := glyz_enlarged_critical_decoupling_fin m hm R hα
    refine ⟨C ^ ((q : ℝ) / 2), Real.rpow_pos_of_pos hC _, fun N f hf => ?_⟩
    have hh := glyz_fintype_square_to_lp_power
      (fun i : Fin (2 ^ N) => f i) hq
      (show 0 ≤ C * (2 : ℝ) ^ ((2 * ε / (q : ℝ)) * N) by positivity)
      (hcrit N (fun i : Fin (2 ^ N) => f i)
        (fun i => hf i (Finset.mem_range.mpr i.isLt)))
    have hcoef :
        (C * (2 : ℝ) ^ ((2 * ε / (q : ℝ)) * N)) ^ ((q : ℝ) / 2) *
          (Fintype.card (Fin (2 ^ N)) : ℝ) ^ ((q : ℝ) / 2 - 1) =
        C ^ ((q : ℝ) / 2) * (2 : ℝ) ^
          (((q : ℝ) - glyzCriticalExponent m / 2 - 1 + ε) * N) := by
      rw [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat,
        glyz_dyadic_power_coefficient hq0 hC.le]
      congr 2
      rw [hqdef]
      ring
    rw [hcoef] at hh
    rw [Fin.sum_univ_eq_sum_range
      (fun i => ∫⁻ x, ENNReal.ofReal (‖f i x‖ ^ (q : ℝ))) (2 ^ N)] at hh
    simpa only [Fin.sum_univ_eq_sum_range] using hh
  · have hpq : (q : ℝ) < p := by
      exact_mod_cast lt_of_le_of_ne hp (Ne.symm heq)
    obtain ⟨M, hM, hinterp⟩ := exists_glyz_affine_boxes_supercritical m hR
    obtain ⟨C, hC, hcrit⟩ := glyz_enlarged_critical_decoupling_fin m hm
      (glyzBoxCutoffRadius m R + 1) hα
    let K := glyzInterpolationFactor p q * C ^ ((q : ℝ) / 2) * M ^ (p : ℝ)
    have hK : 0 < K := mul_pos
      (mul_pos (glyzInterpolationFactor_pos hq0 hpq) (Real.rpow_pos_of_pos hC _))
      (Real.rpow_pos_of_pos hM _)
    refine ⟨K, hK, fun N f hf => ?_⟩
    let L := fun i : Fin (2 ^ N) =>
      glyzMomentFrequencyFrame m (glyzDyadicCenter N i) (glyzDyadicScale N) (glyzDyadicScale_pos N)
    let a := fun i : Fin (2 ^ N) =>
      (EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m (glyzDyadicCenter N i))
    have hh := hinterp (Fin (2 ^ N)) L a q hq p
      (C * (2 : ℝ) ^ ((2 * ε / (q : ℝ)) * N)) hpq (by positivity)
      (hcrit N) (fun i : Fin (2 ^ N) => f i)
      (fun i => hf i (Finset.mem_range.mpr i.isLt))
    have hcoef :
        glyzInterpolationFactor p q *
          (C * (2 : ℝ) ^ ((2 * ε / (q : ℝ)) * N)) ^ ((q : ℝ) / 2) *
          (Fintype.card (Fin (2 ^ N)) : ℝ) ^ ((p : ℝ) - (q : ℝ) / 2 - 1) * M ^ (p : ℝ) =
        K * (2 : ℝ) ^ (((p : ℝ) - glyzCriticalExponent m / 2 - 1 + ε) * N) := by
      rw [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
      calc
        _ = glyzInterpolationFactor p q *
            ((C * (2 : ℝ) ^ ((2 * ε / (q : ℝ)) * N)) ^ ((q : ℝ) / 2) *
              ((2 : ℝ) ^ N) ^ ((p : ℝ) - (q : ℝ) / 2 - 1)) * M ^ (p : ℝ) := by ring
        _ = _ := by
          rw [glyz_dyadic_power_coefficient hq0 hC.le]
          dsimp only [K]
          rw [hqdef]
          ring
    rw [hcoef] at hh
    rw [Fin.sum_univ_eq_sum_range
      (fun i => ∫⁻ x, ENNReal.ofReal (‖f i x‖ ^ (p : ℝ))) (2 ^ N)] at hh
    simpa only [Fin.sum_univ_eq_sum_range] using hh

 /-- The sharp high-p ℓp norm form. Its exponent is the high-p ℓ² loss
 plus the exact finite-family ℓ²-to-ℓp cardinality loss. -/
theorem glyz_supercritical_moment_decoupling (m : ℕ) (hm : 0 < m)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent m ≤ p)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (f : ℕ → SchwartzMap (GlyzSpace m) ℂ),
      GlyzDyadicEnlargedSupported m N R f →
      lpNorm ((∑ i ∈ Finset.range (2 ^ N), f i : SchwartzMap (GlyzSpace m) ℂ) :
          GlyzSpace m → ℂ) p volume ≤
        C * (2 : ℝ) ^
          ((1 - (glyzCriticalExponent m + 2) / (2 * (p : ℝ)) + ε) * N) *
            (∑ i ∈ Finset.range (2 ^ N),
              lpNorm (f i : GlyzSpace m → ℂ) p volume ^ (p : ℝ)) ^ (1 / (p : ℝ)) := by
  have hp0 : 0 < p := lt_of_lt_of_le (show 0 < glyzCriticalNNExponent m from
    glyzCriticalExponent_pos hm) hp
  have hpR : (0 : ℝ) < p := hp0
  obtain ⟨C, hC, h⟩ := glyz_supercritical_moment_power_decoupling m hm hp hR
    (show 0 < ε * (p : ℝ) by positivity)
  refine ⟨C ^ (1 / (p : ℝ)), Real.rpow_pos_of_pos hC _, fun N f hf => ?_⟩
  have hh := glyz_schwartz_lp_of_power_bound (Finset.range (2 ^ N))
    (∑ i ∈ Finset.range (2 ^ N), f i) f hp0
    (show 0 ≤ C * (2 : ℝ) ^
      (((p : ℝ) - glyzCriticalExponent m / 2 - 1 + ε * p) * N) by positivity) (h N f hf)
  have he : (C * (2 : ℝ) ^
      (((p : ℝ) - glyzCriticalExponent m / 2 - 1 + ε * p) * N)) ^ (1 / (p : ℝ)) =
      C ^ (1 / (p : ℝ)) * (2 : ℝ) ^
        ((1 - (glyzCriticalExponent m + 2) / (2 * (p : ℝ)) + ε) * N) := by
    rw [Real.mul_rpow hC.le (by positivity), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 2
    field_simp
    ring
  rwa [he] at hh

end PlanarNikodym
