import PlanarNikodym.Analysis.Sobolev.GeneralSobolevTools

/-! A scaled Sobolev estimate in every finite auxiliary dimension. The
dimension induction uses actual coordinate derivatives and full Fréchet
jets, with a constant depending only on dimension. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff

namespace PlanarNikodym

/-- Pointwise scaled full-jet Sobolev estimate in the actual `Aux d` space.
All norms are extended seminorms; integrability of derivatives is not an
extra hypothesis. The constant `2^d` is independent of scale and input. -/
theorem enorm_le_scaled_fullJet_aux (d : ℕ) {F : Aux d → ℂ}
    (hF : ContDiff ℝ ∞ F) (p : ℝ≥0) (hp : 1 ≤ p) {r : ℝ} (hr : 0 < r) (q : Aux d) :
    ‖F q‖ₑ ≤ (2 : ℝ≥0∞) ^ d * ENNReal.ofReal r ^ (-(d : ℝ) / (p : ℝ)) *
      ∑ j ∈ Finset.range (d + 1), ENNReal.ofReal r ^ j *
        eLpNorm (fun u => ‖iteratedFDeriv ℝ j F u‖) p volume := by
  induction d with
  | zero =>
    have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hp).ne'
    simp only [pow_zero, Nat.cast_zero, neg_zero, zero_div, ENNReal.rpow_zero, one_mul,
      zero_add, Finset.range_one, Finset.sum_singleton, norm_iteratedFDeriv_zero]
    rw [Measure.volume_pi_eq_dirac (0 : Aux 0), eLpNorm_dirac _ _ hp0]
    simp only [enorm_norm, Subsingleton.elim q (0 : Aux 0), le_refl]
  | succ d ih =>
    let R : ℝ≥0∞ := ENNReal.ofReal r
    let A : ℝ≥0∞ := R ^ (-1 / (p : ℝ))
    let C : ℝ≥0∞ := 2 ^ d * R ^ (-(d : ℝ) / (p : ℝ))
    let D := auxHeadDerivative F
    let J : ℕ → ℝ × Aux d → ℝ := fun j x => ‖iteratedFDeriv ℝ j F (Fin.cons x.1 x.2)‖
    let B : ℕ → ℝ≥0∞ := fun j => eLpNorm (fun u => ‖iteratedFDeriv ℝ j F u‖) p volume
    let S₀ : ℝ → ℝ≥0∞ := fun t => ⨆ u : Aux d, ‖F (Fin.cons t u)‖ₑ
    let S₁ : ℝ → ℝ≥0∞ := fun t => ⨆ u : Aux d, ‖D (Fin.cons t u)‖ₑ
    have hD : ContDiff ℝ ∞ D := contDiff_auxHeadDerivative hF
    have hJ (j : ℕ) : Measurable (J j) := by
      simpa only [Function.comp_def, auxConsLinear_apply] using
        (contDiff_infty.mp hF j).continuous_iteratedFDeriv'.norm.measurable.comp
          (auxConsLinear_measurePreserving d).measurable
    have hB (j : ℕ) : eLpNorm (J j) p (volume.prod volume) = B j := by
      simpa only [Function.comp_def, auxConsLinear_apply] using
        (eLpNorm_comp_measurePreserving (f := auxConsLinear d)
          (g := fun u : Aux (d + 1) => ‖iteratedFDeriv ℝ j F u‖)
          (contDiff_infty.mp hF j).continuous_iteratedFDeriv'.norm.aestronglyMeasurable
          (auxConsLinear_measurePreserving d))
    have h₀ (t : ℝ) : S₀ t ≤ C * ∑ j ∈ Finset.range (d + 1),
        R ^ j * eLpNorm (fun u => J j (t, u)) p volume := by
      apply iSup_le
      intro u
      apply (ih (contDiff_cons_slice hF t) u).trans
      apply mul_le_mul_right
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_right
      apply eLpNorm_mono_real
      intro v
      simpa only [norm_norm] using norm_iteratedFDeriv_cons_slice_le hF t v j
    have h₁ (t : ℝ) : S₁ t ≤ C * ∑ j ∈ Finset.range (d + 1),
        R ^ j * eLpNorm (fun u => J (j + 1) (t, u)) p volume := by
      apply iSup_le
      intro u
      apply (ih (contDiff_cons_slice hD t) u).trans
      apply mul_le_mul_right
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_right
      apply eLpNorm_mono_real
      intro v
      simpa only [norm_norm] using (norm_iteratedFDeriv_cons_slice_le hD t v j).trans
        (norm_iteratedFDeriv_auxHeadDerivative_le hF j (Fin.cons t v))
    have hS₀ : eLpNorm S₀ p volume ≤ C * ∑ j ∈ Finset.range (d + 1), R ^ j * B j := by
      have h := eLpNorm_le_weighted_fiber_sum volume volume
        (fun j _ => hJ j) C (fun j => R ^ j) p hp h₀
      simpa only [hB] using h
    have hS₁ : eLpNorm S₁ p volume ≤ C * ∑ j ∈ Finset.range (d + 1), R ^ j * B (j + 1) := by
      have h := eLpNorm_le_weighted_fiber_sum volume volume
        (fun j _ => hJ (j + 1)) C (fun j => R ^ j) p hp h₁
      simpa only [hB] using h
    have hChead : ContDiff ℝ 1 (fun t : ℝ => F (Fin.cons t (Fin.tail q))) := by
      simpa only [Function.comp_def, auxConsLinear_apply, id_eq, Nat.cast_one] using
        contDiff_infty.mp (hF.comp ((auxConsLinear d).contDiff.comp
          (contDiff_id.prodMk (contDiff_const (c := Fin.tail q))))) 1
    have hbase : eLpNorm (fun t : ℝ => F (Fin.cons t (Fin.tail q))) p volume ≤
        eLpNorm S₀ p volume :=
      eLpNorm_mono_enorm (fun t => by
        simp only [enorm_eq_self]
        exact le_iSup_of_le (Fin.tail q) le_rfl)
    have hder : eLpNorm (deriv (fun t : ℝ => F (Fin.cons t (Fin.tail q)))) p volume ≤
        eLpNorm S₁ p volume := by
      apply eLpNorm_mono_enorm
      intro t
      rw [deriv_cons_head hF]
      simp only [enorm_eq_self]
      exact le_iSup_of_le (Fin.tail q) le_rfl
    let S : ℝ≥0∞ := ∑ j ∈ Finset.range (d + 2), R ^ j * B j
    have hlo : (∑ j ∈ Finset.range (d + 1), R ^ j * B j) ≤ S :=
      Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_succ _))
    have hhi : R * (∑ j ∈ Finset.range (d + 1), R ^ j * B (j + 1)) ≤ S := by
      calc
        _ = ∑ j ∈ Finset.range (d + 1), R ^ (j + 1) * B (j + 1) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [pow_succ]
          ring
        _ ≤ S := by
          dsimp [S]
          rw [Finset.sum_range_succ' (f := fun j => R ^ j * B j)]
          exact le_add_right le_rfl
    have hscale : A * C * 2 = (2 : ℝ≥0∞) ^ (d + 1) * R ^ (-((d + 1 : ℕ) : ℝ) / (p : ℝ)) := by
      calc
        _ = 2 ^ (d + 1) * (R ^ (-1 / (p : ℝ)) * R ^ (-(d : ℝ) / (p : ℝ))) := by
          dsimp [A, C]
          rw [pow_succ]
          ring
        _ = _ := by
          rw [← ENNReal.rpow_add _ _ (by dsimp [R]; positivity) ENNReal.ofReal_ne_top]
          congr 1
          congr 1
          push_cast
          ring
    have hpoint := enorm_le_scaled_eLpNorm_add_deriv hChead p hp hr (q 0)
    simp only [Fin.cons_self_tail] at hpoint
    calc
      ‖F q‖ₑ ≤ A * (eLpNorm (fun t => F (Fin.cons t (Fin.tail q))) p volume +
          R * eLpNorm (deriv (fun t => F (Fin.cons t (Fin.tail q)))) p volume) := hpoint
      _ ≤ A * (eLpNorm S₀ p volume + R * eLpNorm S₁ p volume) := by gcongr
      _ ≤ A * (C * (∑ j ∈ Finset.range (d + 1), R ^ j * B j) +
          R * (C * (∑ j ∈ Finset.range (d + 1), R ^ j * B (j + 1)))) := by gcongr
      _ = A * C * ((∑ j ∈ Finset.range (d + 1), R ^ j * B j) +
          R * (∑ j ∈ Finset.range (d + 1), R ^ j * B (j + 1))) := by ring
      _ ≤ A * C * (S + S) := by gcongr
      _ = (A * C * 2) * S := by ring
      _ = _ := by rw [hscale]

theorem iSup_enorm_aux_le_scaled_fullJet (d : ℕ) {F : Aux d → ℂ}
    (hF : ContDiff ℝ ∞ F) (p : ℝ≥0) (hp : 1 ≤ p) {r : ℝ} (hr : 0 < r) :
    (⨆ u : Aux d, ‖F u‖ₑ) ≤ (2 : ℝ≥0∞) ^ d * ENNReal.ofReal r ^ (-(d : ℝ) / (p : ℝ)) *
      ∑ j ∈ Finset.range (d + 1), ENNReal.ofReal r ^ j *
        eLpNorm (fun u => ‖iteratedFDeriv ℝ j F u‖) p volume :=
  iSup_le (enorm_le_scaled_fullJet_aux d hF p hp hr)

end PlanarNikodym
