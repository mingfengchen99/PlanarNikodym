import PlanarNikodym.Analysis.Fourier.GlyzDecouplingConstants
import PlanarNikodym.Analysis.Fourier.GlyzDegreeOne
import PlanarNikodym.Analysis.Fourier.GlyzMomentBoxRescaling

/-! Uniform L² decoupling for the same dyadic families used in the
optimal constants. In degree one this closes the critical base case. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform ENNReal NNReal
namespace PlanarNikodym

theorem glyzMomentFrame_first (m : ℕ) (c : ℝ) (v : Base (m + 1)) :
    glyzMomentFrame (m + 1) c v 0 = v 0 := by
  rw [glyzMomentFrame_apply]
  change (∑ j, glyzMixedMomentMatrix (m + 1) 0 c (c + 1) 0 j * v j) = v 0
  have hj (j : Fin (m + 1)) :
      glyzMixedMomentMatrix (m + 1) 0 c (c + 1) 0 j = if j = 0 then 1 else 0 := by
    have h := glyzMixedMomentMatrix_apply_left (m + 1) 0 c (c + 1) j 0
    have hj0 : j.castAdd 0 = j := Fin.ext rfl
    rw [hj0] at h
    have hc : (j : ℕ) + 1 = 1 ↔ j = 0 := by
      constructor
      · intro hj
        apply Fin.ext
        simpa using hj
      · intro hj
        simp [hj]
    simpa only [glyzMomentCurve, Fin.val_zero, Nat.zero_add, pow_one, iteratedDeriv_fun_id,
      Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, hc] using h
  simp_rw [hj]
  simp

theorem glyzMomentFrequencyFrame_first (m : ℕ) (c δ : ℝ) (hδ : 0 < δ)
    (v : GlyzSpace (m + 1)) :
    glyzMomentFrequencyFrame (m + 1) c δ hδ v 0 = δ * v 0 := by
  change glyzMomentFrame (m + 1) c
    (coefficientDilation (fun j : Fin (m + 1) => δ ^ ((j : ℕ) + 1))
      (fun _ => pow_ne_zero _ hδ.ne') ((EuclideanSpace.equiv (Fin (m + 1)) ℝ) v)) 0 = _
  rw [glyzMomentFrame_first, coefficientDilation_apply]
  simp

theorem glyzMomentFrequencyBox_first (m : ℕ) (c δ : ℝ) (hδ : 0 < δ)
    {ξ : GlyzSpace (m + 1)} (hξ : ξ ∈ glyzMomentFrequencyBox (m + 1) c δ hδ) :
    |ξ 0 - c| ≤ δ := by
  rw [glyzMomentFrequencyBox, glyzFrequencyBox_eq_image] at hξ
  obtain ⟨v, hv, rfl⟩ := hξ
  have hv0 : |v 0| ≤ 1 := by
    exact (norm_le_pi_norm v 0).trans (by simpa using hv)
  change |c ^ (0 + 1) +
    glyzMomentFrequencyFrame (m + 1) c δ hδ ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm v) 0 - c| ≤ δ
  rw [glyzMomentFrequencyFrame_first]
  simpa [abs_mul, abs_of_pos hδ] using
    mul_le_mul_of_nonneg_left hv0 hδ.le

theorem glyz_dyadic_supported_overlap (m N : ℕ)
    (f : ℕ → SchwartzMap (GlyzSpace (m + 1)) ℂ)
    (hf : GlyzDyadicSupported (m + 1) N f) (ξ : GlyzSpace (m + 1)) :
    ((Finset.range (2 ^ N)).filter (fun i => 𝓕 (f i : GlyzSpace (m + 1) → ℂ) ξ ≠ 0)).card ≤ 3 := by
  classical
  apply le_trans (Finset.card_le_card ?_) (glyzLineFrequencyBox_overlap
    (Finset.range (2 ^ N)) (((2 : ℝ) ^ N)⁻¹) (ξ 0))
  intro i hi
  obtain ⟨hi, hfi⟩ := Finset.mem_filter.mp hi
  refine Finset.mem_filter.mpr ⟨hi, ?_⟩
  have hs := glyzMomentFrequencyBox_first m _ _ (by positivity) (hf i hi hfi)
  rw [glyzLineFrequencyBox_eq_Icc (by positivity : 0 < ((2 : ℝ) ^ N)⁻¹)]
  have h := abs_le.mp hs
  constructor <;> linarith

theorem glyz_dyadic_l2_square_bound (m N : ℕ) :
    GlyzDyadicSquareBound (m + 1) N 2 3 := by
  refine ⟨by norm_num, fun f hf => ?_⟩
  have h := glyz_schwartz_l2_overlap (Finset.range (2 ^ N)) f 3
    (glyz_dyadic_supported_overlap m N f hf)
  have he (g : SchwartzMap (GlyzSpace (m + 1)) ℂ) :
      (∫⁻ x, ‖g x‖ₑ ^ (2 : ℕ)) = ENNReal.ofReal (lpNorm (g : GlyzSpace (m + 1) → ℂ)
        2 volume ^ (2 : ℕ)) := by
    rw [ENNReal.ofReal_pow lpNorm_nonneg, ofReal_lpNorm (g.memLp 2 volume)]
    simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] using
      (eLpNorm_nnreal_pow_eq_lintegral (f := (g : GlyzSpace (m + 1) → ℂ))
        (μ := volume) (p := (2 : ℝ≥0)) (by norm_num)).symm
  have hsum : (fun x => ∑ i ∈ Finset.range (2 ^ N), f i x) =
      ((∑ i ∈ Finset.range (2 ^ N), f i : SchwartzMap (GlyzSpace (m + 1)) ℂ) :
        GlyzSpace (m + 1) → ℂ) := by ext x; simp
  have hsumx (x : GlyzSpace (m + 1)) := congrFun hsum x
  simp_rw [hsumx, he] at h
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top 3)
    (ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.ofReal_ne_top)) h
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_mul,
    ENNReal.toReal_natCast, ENNReal.toReal_ofNat, Nat.cast_ofNat, ENNReal.coe_ofNat,
    ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top),
    ← hsum, glyzDyadicSquareEnergy] using ht

theorem glyz_dyadic_l2_constant_le_three (m N : ℕ) :
    glyzDyadicSquareConstant (m + 1) N 2 ≤ 3 :=
  glyzDyadicSquareConstant_le (glyz_dyadic_l2_square_bound m N)

theorem glyz_admissible_l2_loss_zero (m : ℕ) :
    GlyzAdmissibleSquareLoss (m + 1) 2 0 := by
  refine ⟨le_rfl, 3, by norm_num, fun N => ?_⟩
  simpa using glyz_dyadic_l2_constant_le_three m N

theorem glyzOptimalSquareLoss_l2_eq_zero (m : ℕ) :
    glyzOptimalSquareLoss (m + 1) 2 = 0 :=
  le_antisymm (glyzOptimalSquareLoss_le (glyz_admissible_l2_loss_zero m))
    (glyzOptimalSquareLoss_nonneg (m + 1) 2 (by norm_num))

end PlanarNikodym
