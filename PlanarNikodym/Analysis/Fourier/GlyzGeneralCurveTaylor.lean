import PlanarNikodym.Analysis.Fourier.GlyzEnlargedTaylorDecoupling

/-! Uniform Taylor estimates for arbitrary curves with actual finite
regularity and derivative bounds. No decoupling estimate is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped BigOperators
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem glyz_finite_taylor_remainder_bound (f : ℝ → E) (n : ℕ)
    (hf : ContDiff ℝ (n + 1 : ℕ) f) {a b C s : ℝ} (hab : a < b) (hs : s ∈ Icc a b)
    (hC : ∀ u ∈ Icc a b, ‖iteratedDeriv (n + 1) f u‖ ≤ C) :
    ‖f s - glyzTaylorCurve f n a s‖ ≤ C * (s - a) ^ (n + 1) / n.factorial := by
  have hp : taylorWithinEval f n (Icc a b) a s = glyzTaylorCurve f n a s := by
    unfold glyzTaylorCurve
    rw [taylor_within_apply, taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n + 1 := by simp only [Finset.mem_range] at hk; omega
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab)
      (hf.contDiffAt.of_le (by exact_mod_cast hk')) (left_mem_Icc.mpr hab.le), iteratedDerivWithin_univ]
  rw [← hp]
  apply taylor_mean_remainder_bound hab.le hf.contDiffOn hs
  intro u hu
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) hf.contDiffAt hu]
  exact hC u hu

theorem glyz_general_curve_taylor_derivative_bound (l : ℕ) (γ : ℝ → E)
    (hγ : ContDiff ℝ (l + 1 : ℕ) γ) {B a b s : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hab : a < b) (hs : s ∈ Icc a b)
    (hB : ∀ u ∈ Icc (0 : ℝ) 1, ‖iteratedDeriv (l + 1) γ u‖ ≤ B)
    (j : ℕ) (hj : j ≤ l) :
    ‖iteratedDeriv j γ s - iteratedDeriv j (glyzTaylorCurve γ l a) s‖ ≤
      B * (s - a) ^ (l - j + 1) / (l - j).factorial := by
  rw [iteratedDeriv_glyzTaylorCurve _ hj]
  have hfj : ContDiff ℝ (l - j + 1 : ℕ) (iteratedDeriv j γ) := by
    rw [iteratedDeriv_eq_iterate]
    apply ContDiff.iterate_deriv' (l - j + 1) j
    simpa only [show l - j + 1 + j = l + 1 by omega] using hγ
  apply glyz_finite_taylor_remainder_bound _ (l - j) hfj hab hs
  intro u hu
  rw [glyz_iteratedDeriv_order_add, show l - j + 1 + j = l + 1 by omega]
  exact hB u ⟨ha.1.trans hu.1, hu.2.trans hb.2⟩

theorem glyz_general_curve_box_taylor_bound (l : ℕ) {B R : ℝ} (hB : 0 < B) (hR : 0 < R)
    (γ : ℝ → E) (hγ : ContDiff ℝ (l + 1 : ℕ) γ)
    (hder : ∀ u ∈ Icc (0 : ℝ) 1, ‖iteratedDeriv (l + 1) γ u‖ ≤ B)
    {a b s δ : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hab : a < b) (hs : s ∈ Icc a b) (hδ : 0 < δ) (hδb : δ ≤ b - a)
    (v : Base l) (hv : ∀ j, |v j| ≤ R) :
    ‖glyzCurveBoxPoint γ l s δ v - glyzCurveBoxPoint (glyzTaylorCurve γ l a) l s δ v‖ ≤
      ((1 + (l : ℝ) * R) * B) * (b - a) ^ (l + 1) := by
  have hκ : 0 < b - a := sub_pos.mpr hab
  have hsa : 0 ≤ s - a := sub_nonneg.mpr hs.1
  have herr (j : ℕ) (hj : j ≤ l) :
      ‖iteratedDeriv j γ s - iteratedDeriv j (glyzTaylorCurve γ l a) s‖ ≤
        B * (b - a) ^ (l - j + 1) := by
    calc
      _ ≤ B * (s - a) ^ (l - j + 1) / (l - j).factorial :=
        glyz_general_curve_taylor_derivative_bound l γ hγ ha hb hab hs hder j hj
      _ ≤ B * (s - a) ^ (l - j + 1) := div_le_self (by positivity)
        (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (l - j)))
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hsa (sub_le_sub_right hs.2 a) _) hB.le
  have hzero : ‖γ s - glyzTaylorCurve γ l a s‖ ≤ B * (b - a) ^ (l + 1) := by
    simpa only [iteratedDeriv_zero, Nat.sub_zero] using herr 0 (Nat.zero_le l)
  have hterm (j : Fin l) : |δ ^ ((j : ℕ) + 1) * v j| *
      ‖iteratedDeriv ((j : ℕ) + 1) γ s - iteratedDeriv ((j : ℕ) + 1) (glyzTaylorCurve γ l a) s‖ ≤
        R * B * (b - a) ^ (l + 1) := by
    have hcoeff : |δ ^ ((j : ℕ) + 1) * v j| ≤ R * (b - a) ^ ((j : ℕ) + 1) := by
      rw [abs_mul, abs_of_pos (pow_pos hδ _)]
      calc
        _ ≤ (b - a) ^ ((j : ℕ) + 1) * R :=
          mul_le_mul (pow_le_pow_left₀ hδ.le hδb _) (hv j) (abs_nonneg _) (by positivity)
        _ = _ := mul_comm _ _
    calc
      _ ≤ (R * (b - a) ^ ((j : ℕ) + 1)) * (B * (b - a) ^ (l - ((j : ℕ) + 1) + 1)) :=
        mul_le_mul hcoeff (herr _ j.isLt) (norm_nonneg _) (by positivity)
      _ = _ := by
        calc
          _ = R * B * ((b - a) ^ ((j : ℕ) + 1) * (b - a) ^ (l - ((j : ℕ) + 1) + 1)) := by ring
          _ = _ := by rw [← pow_add, show (j : ℕ) + 1 + (l - ((j : ℕ) + 1) + 1) = l + 1 by omega]
  have h := (norm_glyzCurveBoxPoint_sub_le γ (glyzTaylorCurve γ l a) l s δ v).trans
    (add_le_add hzero (Finset.sum_le_sum fun j _ => hterm j))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  convert h using 1 <;> (first | rfl | ring)

/-- Bounded derivatives and a positive actual jet determinant give
uniform inverse bounds before the curve is chosen. -/
theorem exists_uniform_glyz_general_curve_inverse (l : ℕ) {β B : ℝ} (hβ : 0 < β) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ → GlyzSpace l) (s : ℝ),
      (∀ j : Fin l, ‖iteratedDeriv ((j : ℕ) + 1) γ s‖ ≤ B) →
      β ≤ |(glyzCurveJetOperator γ s).det| →
      ∃ L : GlyzSpace l ≃L[ℝ] GlyzSpace l,
        L.toContinuousLinearMap = glyzCurveJetOperator γ s ∧ ‖L.symm.toContinuousLinearMap‖ ≤ C := by
  obtain ⟨C, hC, hinv⟩ := exists_uniform_glyz_frame_inverse (E := GlyzSpace l) hβ ((l : ℝ) * B)
  refine ⟨C, hC, fun γ s hder hdet => ?_⟩
  have hd : (glyzCurveJetOperator γ s).det ≠ 0 := by intro hz; rw [hz, abs_zero] at hdet; linarith
  let L := (glyzCurveJetOperator γ s).toContinuousLinearEquivOfDetNeZero hd
  refine ⟨L, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ hd, ?_⟩
  exact hinv L (norm_glyzCurveJetOperator_le γ s hB.le hder) hdet

theorem exists_uniform_glyz_general_taylor_inverse (l : ℕ) {β B : ℝ} (hβ : 0 < β) (hB : 0 < B) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 0 < C ∧ ∀ γ : ℝ → GlyzSpace l,
      ContDiff ℝ (l + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ l + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, a < b → b - a < ρ →
      ∀ s ∈ Icc a b, ∃ T : GlyzSpace l ≃L[ℝ] GlyzSpace l,
        T.toContinuousLinearMap = glyzCurveJetOperator (glyzTaylorCurve γ l a) s ∧
        ‖T.symm.toContinuousLinearMap‖ ≤ C := by
  obtain ⟨ε, C, hε, hC, hstable⟩ := exists_uniform_glyz_frame_perturbation (E := GlyzSpace l) hβ ((l : ℝ) * B)
  obtain ⟨_, _, hframes⟩ := exists_uniform_glyz_general_curve_inverse l hβ hB
  let q : ℝ := (l : ℝ) * B + 1
  have hq : 0 < q := by dsimp [q]; positivity
  refine ⟨min 1 (ε / q), C, lt_min zero_lt_one (div_pos hε hq), min_le_left _ _, hC, ?_⟩
  intro γ hγ hder hdet a ha b hb hab hρ s hs
  have hκ : 0 < b - a := sub_pos.mpr hab
  have hκ1 : b - a ≤ 1 := (hρ.trans_le (min_le_left _ _)).le
  have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨ha.1.trans hs.1, hs.2.trans hb.2⟩
  have hsmall : (l : ℝ) * B * (b - a) < ε := by
    have h := (lt_div_iff₀ hq).mp (hρ.trans_le (min_le_right _ _))
    dsimp [q] at h
    nlinarith
  have hjets (j : Fin l) :
      ‖iteratedDeriv ((j : ℕ) + 1) γ s - iteratedDeriv ((j : ℕ) + 1) (glyzTaylorCurve γ l a) s‖ ≤ B * (b - a) := by
    calc
      _ ≤ B * (s - a) ^ (l - ((j : ℕ) + 1) + 1) / (l - ((j : ℕ) + 1)).factorial :=
        glyz_general_curve_taylor_derivative_bound l γ hγ ha hb hab hs (fun u hu => hder u hu _ le_rfl) _ j.isLt
      _ ≤ B * (s - a) ^ (l - ((j : ℕ) + 1) + 1) := div_le_self (by positivity [sub_nonneg.mpr hs.1])
        (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (l - ((j : ℕ) + 1))))
      _ ≤ B * (b - a) ^ (l - ((j : ℕ) + 1) + 1) := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (sub_nonneg.mpr hs.1) (sub_le_sub_right hs.2 a) _) hB.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_of_le_one hκ.le hκ1 (by omega)) hB.le
  obtain ⟨L, hL, _⟩ := hframes γ s (fun j => hder s hs01 _ (by omega)) (hdet s hs01)
  apply hstable L
  · rw [hL]; exact norm_glyzCurveJetOperator_le γ s hB.le (fun j => hder s hs01 _ (by omega))
  · change β ≤ |L.toContinuousLinearMap.det|
    rw [hL]; exact hdet s hs01
  · rw [hL, dist_eq_norm, norm_sub_rev]
    exact (norm_glyzCurveJetOperator_sub_le _ _ s (mul_nonneg hB.le hκ.le) hjets).trans_lt
      (by simpa only [mul_assoc] using hsmall)

end PlanarNikodym
