import PlanarNikodym.Analysis.Fourier.GlyzGeneralCurveTaylor

/-! Actual curve arcs lie in uniformly enlarged derivative boxes.
The two-sided Taylor argument applies to midpoint-based time pieces,
including both ends of the parameter interval. -/
noncomputable section
open Set Metric
open scoped BigOperators
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem glyzTaylorCurve_comp_neg (γ : ℝ → E) (k : ℕ) (c t : ℝ) :
    glyzTaylorCurve (fun u => γ (-u)) k (-c) (-t) = glyzTaylorCurve γ k c t := by
  rw [glyzTaylorCurve_eq_sum, glyzTaylorCurve_eq_sum]
  simp only [neg_neg, iteratedDeriv_comp_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul]
  congr 1
  calc
    _ = ((((j : ℕ) + 1).factorial : ℝ)⁻¹) *
        (((-t - -c) * (-1)) ^ ((j : ℕ) + 1)) := by rw [mul_pow]; ring
    _ = _ := by congr 2; ring

theorem glyz_two_sided_taylor_remainder (γ : ℝ → E) (k : ℕ)
    (hγ : ContDiff ℝ (k + 1 : ℕ) γ) {B c t : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hder : ∀ u ∈ Icc (0 : ℝ) 1, ‖iteratedDeriv (k + 1) γ u‖ ≤ B) :
    ‖γ t - glyzTaylorCurve γ k c t‖ ≤ B * |t - c| ^ (k + 1) / k.factorial := by
  rcases lt_trichotomy c t with hct | rfl | htc
  · have h := glyz_finite_taylor_remainder_bound γ k hγ hct
      (right_mem_Icc.mpr hct.le) (fun u hu => hder u ⟨hc.1.trans hu.1, hu.2.trans ht.2⟩)
    simpa only [abs_of_nonneg (sub_nonneg.mpr hct.le)] using h
  · simp [glyzTaylorCurve_eq_sum]
  · have hγn : ContDiff ℝ (k + 1 : ℕ) (fun u => γ (-u)) := hγ.comp contDiff_neg
    have h := glyz_finite_taylor_remainder_bound (fun u => γ (-u)) k hγn
      (neg_lt_neg htc) (right_mem_Icc.mpr (neg_le_neg htc.le)) (C := B) (by
        intro u hu
        have hu' : -u ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hu.2, ht.1], by linarith [hu.1, hc.2]⟩
        simpa only [iteratedDeriv_comp_neg, norm_smul, norm_pow, norm_neg,
          norm_one, one_pow, one_mul] using hder (-u) hu')
    rw [neg_neg, glyzTaylorCurve_comp_neg] at h
    simpa only [abs_of_nonpos (sub_nonpos.mpr htc.le), neg_sub,
      show -t - -c = c - t by ring] using h

theorem glyzTaylorCurve_mem_curveBox (k : ℕ) (γ : ℝ → E) {c t δ : ℝ}
    (hδ : 0 < δ) (ht : |t - c| ≤ δ) :
    glyzTaylorCurve γ k c t ∈ glyzCurveBox γ k c δ := by
  let v : Base k := fun j => (((j : ℕ) + 1).factorial : ℝ)⁻¹ *
    ((t - c) / δ) ^ ((j : ℕ) + 1)
  refine ⟨v, ?_, ?_⟩
  · intro j
    have hf : (1 : ℝ) ≤ (((j : ℕ) + 1).factorial : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos _)
    have hr : |(t - c) / δ| ≤ 1 := by
      rw [abs_div, abs_of_pos hδ]
      exact (div_le_one hδ).mpr ht
    dsimp [v]
    rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < (((j : ℕ) + 1).factorial : ℝ)), abs_pow]
    exact (mul_le_mul (inv_le_one_of_one_le₀ hf) (pow_le_one₀ (abs_nonneg _) hr)
      (by positivity) zero_le_one).trans_eq (one_mul 1)
  · rw [glyzTaylorCurve_eq_sum]
    unfold glyzCurveBoxPoint
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    dsimp [v]
    rw [div_pow]
    field_simp

theorem exists_uniform_glyz_curve_arc_support (k : ℕ) {β B : ℝ}
    (hβ : 0 < β) (hB : 0 < B) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ γ : ℝ → GlyzSpace k,
      ContDiff ℝ (k + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ k + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ c ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → |t - c| ≤ δ →
      γ t ∈ glyzEnlargedCurveBox γ k c δ Q := by
  obtain ⟨C, hC, hframe⟩ := exists_uniform_glyz_general_curve_inverse k hβ hB
  refine ⟨1 + C * B, by positivity, fun γ hγ hder hdet c hc t ht δ hδ hδ1 htc => ?_⟩
  obtain ⟨L, hL, hLi⟩ := hframe γ c (fun j => hder c hc _ (by omega)) (hdet c hc)
  have herr : ‖γ t - glyzTaylorCurve γ k c t‖ ≤ B * δ ^ k := by
    calc
      _ ≤ B * |t - c| ^ (k + 1) / k.factorial :=
        glyz_two_sided_taylor_remainder γ k hγ hc ht (fun u hu => hder u hu _ le_rfl)
      _ ≤ B * |t - c| ^ (k + 1) := div_le_self (by positivity)
        (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos k))
      _ ≤ B * δ ^ (k + 1) := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) htc _) hB.le
      _ ≤ B * δ ^ k := mul_le_mul_of_nonneg_left (by
        rw [pow_succ]
        exact mul_le_of_le_one_right (pow_nonneg hδ.le _) hδ1) hB.le
  have hp := glyzTaylorCurve_mem_curveBox k γ hδ htc
  change glyzTaylorCurve γ k c t ∈ glyzEnlargedCurveBox γ k c δ 1 at hp
  rw [glyzEnlargedCurveBox_eq_frequencyBox γ c δ 1 hδ zero_le_one L hL] at hp
  rw [glyzEnlargedCurveBox_eq_frequencyBox γ c δ (1 + C * B) hδ (by positivity) L hL]
  apply glyz_scaled_box_add_ball_subset L hδ hδ1 hC.le hLi (γ c)
  exact ⟨glyzTaylorCurve γ k c t, hp, γ t - glyzTaylorCurve γ k c t,
    by simpa only [mem_closedBall, dist_zero_right] using herr, by abel_nf⟩

end PlanarNikodym
