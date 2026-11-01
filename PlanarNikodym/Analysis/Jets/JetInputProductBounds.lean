import PlanarNikodym.Analysis.Jets.JetAmplitudeExpansion
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Pointwise bounds for every full derivative of the input product used
in the finite amplitude expansion. The constants depend only on the order. -/
noncomputable section
open Set
open scoped ContDiff

namespace PlanarNikodym

private theorem norm_iteratedFDeriv_fst_le (j : ℕ) (c : ℂ) (x : Plane) :
    ‖iteratedFDeriv ℝ j (fun y : ℂ × Plane => y.1) (c, x)‖ ≤ 1 + ‖c‖ := by
  cases j with
  | zero =>
    simpa only [norm_iteratedFDeriv_zero] using (le_add_of_nonneg_left zero_le_one : ‖c‖ ≤ 1 + ‖c‖)
  | succ j =>
    rw [← norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ (fun y : ℂ × Plane => y.1) =
        fun _ => ContinuousLinearMap.fst ℝ ℂ Plane := by
      funext y
      exact (ContinuousLinearMap.fst ℝ ℂ Plane).fderiv
    rw [he]
    cases j with
    | zero =>
      rw [norm_iteratedFDeriv_zero]
      exact (ContinuousLinearMap.norm_fst_le ℝ ℂ Plane).trans (le_add_of_nonneg_right (norm_nonneg c))
    | succ j => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]; positivity

/-- Pulling the input back along the second projection costs no operator norm. -/
theorem norm_iteratedFDeriv_comp_snd_le {f : Plane → ℂ}
    (hf : ContDiff ℝ ∞ f) (j : ℕ) (c : ℂ) (x : Plane) :
    ‖iteratedFDeriv ℝ j (fun y : ℂ × Plane => f y.2) (c, x)‖ ≤
      ‖iteratedFDeriv ℝ j f x‖ := by
  let L := ContinuousLinearMap.snd ℝ ℂ Plane
  change ‖iteratedFDeriv ℝ j (f ∘ L) (c, x)‖ ≤ _
  rw [L.iteratedFDeriv_comp_right (contDiff_infty.mp hf j) (c, x) le_rfl]
  refine ((iteratedFDeriv ℝ j f x).norm_compContinuousLinearMap_le
    (fun _ : Fin j => L)).trans ?_
  calc
    ‖iteratedFDeriv ℝ j f x‖ * ∏ _ : Fin j, ‖L‖ ≤
        ‖iteratedFDeriv ℝ j f x‖ * ∏ _ : Fin j, (1 : ℝ) := by
      gcongr
      exact ContinuousLinearMap.norm_snd_le ℝ ℂ Plane
    _ = ‖iteratedFDeriv ℝ j f x‖ := by simp

/-- Every full jet of `(c,x) ↦ c * f x` is bounded by the finite input jet
sum. The explicit constant `2^j` is independent of the input and the point. -/
theorem norm_iteratedFDeriv_jetInputProduct_le {f : Plane → ℂ}
    (hf : ContDiff ℝ ∞ f) (j : ℕ) (c : ℂ) (x : Plane) :
    ‖iteratedFDeriv ℝ j (jetInputProduct f) (c, x)‖ ≤
      (2 : ℝ) ^ j * (1 + ‖c‖) *
        ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i f x‖ := by
  classical
  let S := ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i f x‖
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hjet : ∀ i, i ≤ j → ‖iteratedFDeriv ℝ i f x‖ ≤ S := by
    intro i hi
    exact Finset.single_le_sum (fun n _ => norm_nonneg (iteratedFDeriv ℝ n f x))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  have hm := norm_iteratedFDeriv_mul_le
    (contDiff_fst : ContDiff ℝ j (fun y : ℂ × Plane => y.1))
    ((contDiff_infty.mp hf j).comp contDiff_snd) (c, x) (n := j) le_rfl
  change ‖iteratedFDeriv ℝ j (jetInputProduct f) (c, x)‖ ≤ _ at hm
  calc
    ‖iteratedFDeriv ℝ j (jetInputProduct f) (c, x)‖ ≤
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun y : ℂ × Plane => y.1) (c, x)‖ *
          ‖iteratedFDeriv ℝ (j - i) (fun y : ℂ × Plane => f y.2) (c, x)‖ := hm
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (1 + ‖c‖) * S := by
      apply Finset.sum_le_sum
      intro i hi
      gcongr
      · exact norm_iteratedFDeriv_fst_le i c x
      · exact (norm_iteratedFDeriv_comp_snd_le hf (j - i) c x).trans (hjet _ (Nat.sub_le _ _))
    _ = (2 : ℝ) ^ j * (1 + ‖c‖) * S := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hs : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
        exact_mod_cast Nat.sum_range_choose j
      rw [hs]

/-- A common finite-order bound, using the same input jet sum for every
order at most `s`. -/
theorem norm_iteratedFDeriv_jetInputProduct_le_of_le {f : Plane → ℂ}
    (hf : ContDiff ℝ ∞ f) {j s : ℕ} (hjs : j ≤ s) (c : ℂ) (x : Plane) :
    ‖iteratedFDeriv ℝ j (jetInputProduct f) (c, x)‖ ≤
      (2 : ℝ) ^ s * (1 + ‖c‖) *
        ∑ i ∈ Finset.range (s + 1), ‖iteratedFDeriv ℝ i f x‖ := by
  refine (norm_iteratedFDeriv_jetInputProduct_le hf j c x).trans ?_
  gcongr
  norm_num

/-- Summing all full derivatives up to order `s` costs the explicit
positive constant `(s+1) * 2^s`. -/
theorem sum_norm_iteratedFDeriv_jetInputProduct_le {f : Plane → ℂ}
    (hf : ContDiff ℝ ∞ f) (s : ℕ) (c : ℂ) (x : Plane) :
    (∑ j ∈ Finset.range (s + 1), ‖iteratedFDeriv ℝ j (jetInputProduct f) (c, x)‖) ≤
      ((s + 1 : ℕ) : ℝ) * (2 : ℝ) ^ s * (1 + ‖c‖) *
        ∑ i ∈ Finset.range (s + 1), ‖iteratedFDeriv ℝ i f x‖ := by
  calc
    (∑ j ∈ Finset.range (s + 1), ‖iteratedFDeriv ℝ j (jetInputProduct f) (c, x)‖) ≤
        ∑ _j ∈ Finset.range (s + 1), (2 : ℝ) ^ s * (1 + ‖c‖) *
          ∑ i ∈ Finset.range (s + 1), ‖iteratedFDeriv ℝ i f x‖ := by
      apply Finset.sum_le_sum
      intro j hj
      exact norm_iteratedFDeriv_jetInputProduct_le_of_le hf
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) c x
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- A single strictly positive constant works for every smooth input
and every point at the fixed finite derivative order. -/
theorem exists_sum_norm_iteratedFDeriv_jetInputProduct_bound (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Plane → ℂ), ContDiff ℝ ∞ f → ∀ (c : ℂ) (x : Plane),
      (∑ j ∈ Finset.range (s + 1), ‖iteratedFDeriv ℝ j (jetInputProduct f) (c, x)‖) ≤
        C * (1 + ‖c‖) * ∑ i ∈ Finset.range (s + 1), ‖iteratedFDeriv ℝ i f x‖ := by
  refine ⟨((s + 1 : ℕ) : ℝ) * (2 : ℝ) ^ s, by positivity, ?_⟩
  intro f hf c x
  exact sum_norm_iteratedFDeriv_jetInputProduct_le hf s c x

end PlanarNikodym
