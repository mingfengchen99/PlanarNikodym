import PlanarNikodym.Analysis.Fourier.GlyzCurveJetInverse
import PlanarNikodym.Analysis.Fourier.GlyzFramePerturbation
import PlanarNikodym.Analysis.Fourier.GlyzTaylorJets

/-! Uniformly invertible Taylor jet frames on sufficiently short
intervals. All frames come from the actual projected curves. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped BigOperators
namespace PlanarNikodym

theorem norm_glyzCurveJetOperator_sub_le {l : ℕ} (γ P : ℝ → GlyzSpace l) (s : ℝ)
    {D : ℝ} (hD : 0 ≤ D)
    (hjet : ∀ j : Fin l,
      ‖iteratedDeriv ((j : ℕ) + 1) γ s - iteratedDeriv ((j : ℕ) + 1) P s‖ ≤ D) :
    ‖glyzCurveJetOperator γ s - glyzCurveJetOperator P s‖ ≤ (l : ℝ) * D := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have he : (glyzCurveJetOperator γ s - glyzCurveJetOperator P s) v =
      ∑ j : Fin l, v j • (iteratedDeriv ((j : ℕ) + 1) γ s -
        iteratedDeriv ((j : ℕ) + 1) P s) := by
    simp only [sub_apply, glyzCurveJetOperator_apply,
      smul_sub, Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ j : Fin l, ‖v j • (iteratedDeriv ((j : ℕ) + 1) γ s -
        iteratedDeriv ((j : ℕ) + 1) P s)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin l, ‖v‖ * D := Finset.sum_le_sum fun j _ => by
      rw [norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le v j) (hjet j) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]; ring

theorem exists_uniform_glyzTaylorCurve_inverse (l r : ℕ) {ν : ℝ} (hν : 0 < ν) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 0 < C ∧ ∀ t a b : ℝ,
      a ∈ Icc (-1 : ℝ) 1 → b ∈ Icc (-1 : ℝ) 1 → a < b → b - a < ρ →
      ∀ s ∈ Icc a b, (s, t) ∈ separatedMixedCenters ν →
        ∃ T : GlyzSpace l ≃L[ℝ] GlyzSpace l,
          T.toContinuousLinearMap =
            glyzCurveJetOperator (glyzTaylorCurve (glyzCoordinateCurve l r t) l a) s ∧
          ‖T.symm.toContinuousLinearMap‖ ≤ C := by
  obtain ⟨β, B, hβ, hB, _, hder, hdet⟩ :=
    exists_uniform_glyzCoordinateCurve_certificate l r l hν
  obtain ⟨ε, C, hε, hC, hstable⟩ :=
    exists_uniform_glyz_frame_perturbation (E := GlyzSpace l) hβ ((l : ℝ) * B)
  obtain ⟨D, hD, htaylor⟩ := exists_uniform_glyzCoordinateCurve_taylor_bound l r
  obtain ⟨_, _, hframes⟩ := exists_uniform_glyzCoordinateCurve_inverse l r hν
  let q : ℝ := (l : ℝ) * D + 1
  have hq : 0 < q := by dsimp [q]; positivity
  refine ⟨min 1 (ε / q), C, lt_min zero_lt_one (div_pos hε hq),
    min_le_left _ _, hC, ?_⟩
  intro t a b ha hb hab hρ s hs hsep
  have hκ : 0 < b - a := sub_pos.mpr hab
  have hκ1 : b - a ≤ 1 := (hρ.trans_le (min_le_left _ _)).le
  have hsmall : (l : ℝ) * D * (b - a) < ε := by
    have h := (lt_div_iff₀ hq).mp (hρ.trans_le (min_le_right _ _))
    dsimp [q] at h
    nlinarith
  have hjets (j : Fin l) :
      ‖iteratedDeriv ((j : ℕ) + 1) (glyzCoordinateCurve l r t) s -
        iteratedDeriv ((j : ℕ) + 1)
          (glyzTaylorCurve (glyzCoordinateCurve l r t) l a) s‖ ≤ D * (b - a) := by
    have hj : (j : ℕ) + 1 ≤ l := j.isLt
    have hsa : 0 ≤ s - a := sub_nonneg.mpr hs.1
    calc
      _ ≤ D * (s - a) ^ (l - ((j : ℕ) + 1) + 1) / (l - ((j : ℕ) + 1)).factorial :=
        htaylor t a b ha hb hab s hs _ hj
      _ ≤ D * (s - a) ^ (l - ((j : ℕ) + 1) + 1) :=
        div_le_self (by positivity) (by exact_mod_cast (Nat.succ_le_of_lt
          (Nat.factorial_pos (l - ((j : ℕ) + 1)))))
      _ ≤ D * (b - a) ^ (l - ((j : ℕ) + 1) + 1) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (sub_nonneg.mpr hs.1) (sub_le_sub_right hs.2 a) _) hD.le
      _ ≤ D * (b - a) := mul_le_mul_of_nonneg_left
        (pow_le_of_le_one hκ.le hκ1 (by omega)) hD.le
  obtain ⟨L, hL, _⟩ := hframes (s, t) hsep
  apply hstable L
  · rw [hL]
    exact norm_glyzCurveJetOperator_le _ _ hB.le
      (fun j => hder t s hsep.1 _ j.isLt)
  · change β ≤ |L.toContinuousLinearMap.det|
    rw [hL, det_glyzCurveJetOperator]
    exact hdet (s, t) hsep
  · rw [hL, dist_eq_norm, norm_sub_rev]
    exact (norm_glyzCurveJetOperator_sub_le _ _ s (mul_nonneg hD.le hκ.le) hjets).trans_lt
      (by simpa only [mul_assoc] using hsmall)

end PlanarNikodym
