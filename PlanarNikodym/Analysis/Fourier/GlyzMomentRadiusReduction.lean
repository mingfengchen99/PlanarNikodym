import PlanarNikodym.Analysis.Fourier.GlyzDyadicBlockSupport

/-! A fixed enlargement of fine moment boxes is absorbed by grouping a
fixed number of dyadic generations. This supplies the radius change
needed by localization, without assuming a new decoupling estimate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped FourierTransform NNReal ENNReal
namespace PlanarNikodym

theorem glyzMomentFrame_zero_apply (m : ℕ) (v : Base m) (k : Fin m) :
    glyzMomentFrame m 0 v k = (((k : ℕ) + 1).factorial : ℝ) * v k := by
  rw [glyzMomentFrame_apply]
  change (∑ j, glyzMixedMomentMatrix m 0 0 (0 + 1) k j * v j) = _
  have he (j : Fin m) :
      glyzMixedMomentMatrix m 0 0 (0 + 1) k j =
        if j = k then (((k : ℕ) + 1).factorial : ℝ) else 0 := by
    have hj := glyzMixedMomentMatrix_apply_left m 0 0 (0 + 1) j k
    have hj0 : j.castAdd 0 = j := Fin.ext rfl
    rw [hj0] at hj
    simpa only [glyzMomentCurve, iteratedDeriv_fun_pow_zero,
      Nat.add_left_inj, Fin.val_inj, Nat.cast_ite, Nat.cast_zero] using hj
  simp_rw [he]
  simp

theorem glyzMomentFrame_zero_symm_curve (m : ℕ) (s : ℝ) :
    (glyzMomentFrame m 0).symm (glyzMomentCurve m s) =
      fun j : Fin m => s ^ ((j : ℕ) + 1) / (((j : ℕ) + 1).factorial : ℝ) := by
  apply (glyzMomentFrame m 0).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  ext j
  rw [glyzMomentFrame_zero_apply]
  dsimp [glyzMomentCurve]
  field_simp

theorem glyzMomentFrame_zero_curve_norm (m : ℕ) {s : ℝ} (hs : |s| ≤ 1 / 2) :
    ‖(glyzMomentFrame m 0).symm (glyzMomentCurve m s)‖ ≤ 1 / 2 := by
  rw [glyzMomentFrame_zero_symm_curve]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr
  intro j
  have hf : (1 : ℝ) ≤ (((j : ℕ) + 1).factorial : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos _)
  have hp : |s| ^ ((j : ℕ) + 1) ≤ |s| := by
    calc
      _ = |s| ^ (j : ℕ) * |s| := pow_succ _ _
      _ ≤ 1 * |s| := mul_le_mul_of_nonneg_right
        (pow_le_one₀ (abs_nonneg _) (hs.trans (by norm_num))) (abs_nonneg _)
      _ = _ := one_mul _
  rw [Real.norm_eq_abs, abs_div, abs_pow,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (((j : ℕ) + 1).factorial : ℝ))]
  exact (div_le_self (by positivity) hf).trans (hp.trans hs)

theorem exists_glyz_normalized_enlarged_box_small_scale (m : ℕ) (R : ℝ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
      ∀ s : ℝ, |s| ≤ 1 / 2 → ∀ ρ : ℝ, ∀ hρ : 0 < ρ, ρ ≤ η →
      glyzFrequencyBox (glyzMomentFrequencyFrame m s ρ hρ)
        ((EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m s)) R ⊆
          glyzMomentFrequencyBox m 0 1 zero_lt_one := by
  let Q := (glyzMomentFrequencyFrame m 0 1 zero_lt_one).symm.trans
    (EuclideanSpace.equiv (Fin m) ℝ)
  let E : (ℝ × ℝ) × Base m → Base m := fun z =>
    Q (∑ j : Fin m, (z.1.2 ^ (j : ℕ) * z.2 j) • glyzEuclideanJetBlock m m z.1.1 j)
  have hc : Continuous E := by
    apply Q.continuous.comp
    apply continuous_finsetSum
    intro j _
    exact (((continuous_fst.snd).pow _).mul
      ((show Continuous (fun v : Base m => v j) from continuous_apply j).comp continuous_snd)).smul
      ((continuous_glyzEuclideanJetBlock m m j).comp continuous_fst.fst)
  have hk : IsCompact (((Icc (-1 / 2 : ℝ) (1 / 2)) ×ˢ Icc (0 : ℝ) 1) ×ˢ
      closedBall (0 : Base m) R) :=
    (isCompact_Icc.prod isCompact_Icc).prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hk.exists_bound_of_continuousOn hc.continuousOn
  let η := min 1 ((1 / 2) / (|C| + 1))
  have hη : 0 < η := lt_min zero_lt_one (by positivity)
  refine ⟨η, hη, min_le_left _ _, fun s hs ρ hρ hρη ξ hξ => ?_⟩
  rw [glyzFrequencyBox_eq_image] at hξ
  obtain ⟨v, hv, rfl⟩ := hξ
  have hρ1 : ρ ≤ 1 := hρη.trans (min_le_left _ _)
  have hbound : ‖E ((s, ρ), v)‖ ≤ |C| + 1 :=
    (hC ((s, ρ), v) ⟨⟨by simpa only [mem_Icc, neg_div] using abs_le.mp hs,
      ⟨hρ.le, hρ1⟩⟩, hv⟩).trans (by linarith [le_abs_self C])
  have hsmall : ρ * (|C| + 1) ≤ 1 / 2 := by
    exact (le_div_iff₀ (by positivity)).mp (hρη.trans (min_le_right _ _))
  have hq (w : Base m) :
      Q ((EuclideanSpace.equiv (Fin m) ℝ).symm w) = (glyzMomentFrame m 0).symm w := by
    change (coefficientDilation (fun j : Fin m => (1 : ℝ) ^ ((j : ℕ) + 1))
      (fun _ => pow_ne_zero _ zero_lt_one.ne')).symm ((glyzMomentFrame m 0).symm w) = _
    ext j
    simp
  change ‖Q (_ - (EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m 0))‖ ≤ 1
  have hz : glyzMomentCurve m 0 = 0 := by ext j; simp [glyzMomentCurve]
  rw [hz, map_zero, sub_zero, map_add, hq, glyzMomentFrequencyFrame_coordinates]
  have he : Q (∑ j : Fin m, (ρ ^ ((j : ℕ) + 1) * v j) •
      glyzEuclideanJetBlock m m s j) = ρ • E ((s, ρ), v) := by
    change Q _ = ρ • Q (∑ j : Fin m, (ρ ^ (j : ℕ) * v j) •
      glyzEuclideanJetBlock m m s j)
    rw [← map_smul, Finset.smul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul, pow_succ]
    congr 1
    ring
  rw [he]
  calc
    _ ≤ ‖(glyzMomentFrame m 0).symm (glyzMomentCurve m s)‖ + ‖ρ • E ((s, ρ), v)‖ :=
      norm_add_le _ _
    _ ≤ 1 / 2 + ρ * (|C| + 1) := add_le_add (glyzMomentFrame_zero_curve_norm m hs)
      (by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
          exact mul_le_mul_of_nonneg_left hbound hρ.le)
    _ ≤ 1 := by linarith

theorem exists_glyz_enlarged_box_small_scale (m : ℕ) (R : ℝ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
      ∀ (c κ s ρ : ℝ) (hκ : 0 < κ) (hρ : 0 < ρ),
      |s| ≤ 1 / 2 → ρ ≤ η →
      glyzFrequencyBox (glyzMomentFrequencyFrame m (c + κ * s) (κ * ρ) (mul_pos hκ hρ))
        ((EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m (c + κ * s))) R ⊆
          glyzMomentFrequencyBox m c κ hκ := by
  obtain ⟨η, hη, hη1, h⟩ := exists_glyz_normalized_enlarged_box_small_scale m R
  refine ⟨η, hη, hη1, fun c κ s ρ hκ hρ hs hρη => ?_⟩
  have hp := glyzMomentFrequencyBox_affine_image m c κ 0 1 hκ zero_lt_one
  simp only [mul_zero, add_zero] at hp
  have hscale : glyzMomentFrequencyBox m c (κ * 1) (mul_pos hκ zero_lt_one) =
      glyzMomentFrequencyBox m c κ hκ := by
    congr 1
    exact mul_one κ
  rw [hscale] at hp
  rw [← glyzMomentFrequencyBox_affine_image_radius m c κ s ρ R hκ hρ, ← hp]
  exact Set.image_mono (h s hs ρ hρ hρη)

/-- A fixed number of extra dyadic generations absorbs any fixed radius.
The depth is chosen before the parent interval or its location. -/
theorem exists_glyz_dyadic_radius_reduction (m : ℕ) (R : ℝ) :
    ∃ q : ℕ, ∀ n i j : ℕ, j < 2 ^ q →
      glyzFrequencyBox (glyzMomentFrequencyFrame m
        (glyzDyadicCenter (n + q) (i * 2 ^ q + j)) (glyzDyadicScale (n + q))
        (glyzDyadicScale_pos (n + q)))
        ((EuclideanSpace.equiv (Fin m) ℝ).symm
          (glyzMomentCurve m (glyzDyadicCenter (n + q) (i * 2 ^ q + j)))) R ⊆
      glyzMomentFrequencyBox m (glyzDyadicCenter n i) (glyzDyadicScale n)
        (glyzDyadicScale_pos n) := by
  obtain ⟨η, hη, _, h⟩ := exists_glyz_enlarged_box_small_scale m R
  obtain ⟨q, hq⟩ := exists_pow_lt_of_lt_one hη (by norm_num : (1 / 2 : ℝ) < 1)
  have hq' : glyzDyadicScale q ≤ η := by
    simpa [glyzDyadicScale, one_div, inv_pow] using hq.le
  refine ⟨q, fun n i j hj => ?_⟩
  have hs : |glyzDyadicCenter q j - 1 / 2| ≤ 1 / 2 := by
    have hjc := glyzDyadicCenter_mem_Icc hj
    exact abs_le.mpr ⟨by linarith [hjc.1], by linarith [hjc.2]⟩
  have hc : glyzDyadicCenter n i + glyzDyadicScale n * (glyzDyadicCenter q j - 1 / 2) =
      glyzDyadicCenter (n + q) (i * 2 ^ q + j) := by
    rw [← glyzDyadicCenter_rescale]
    unfold glyzDyadicCenter
    ring
  have ht := h (glyzDyadicCenter n i) (glyzDyadicScale n) (glyzDyadicCenter q j - 1 / 2)
    (glyzDyadicScale q) (glyzDyadicScale_pos n) (glyzDyadicScale_pos q) hs hq'
  rw [hc] at ht
  convert ht using 1
  congr 2
  exact glyzDyadicScale_add n q

end PlanarNikodym
