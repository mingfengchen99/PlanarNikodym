import PlanarNikodym.Geometry.AnalyticSignCellBarrier
import Mathlib.Analysis.Normed.Group.Bounded

/-! A positive coordinate tilt removes the need to exclude compact fiber
components by a common-complement argument. At any nonzero vertical
direction, one of the actual positive analytic barriers has nonzero
directional derivative, while all retain the same vanishing boundary. -/
noncomputable section
open Set
namespace PlanarNikodym

theorem exists_positive_barrier_tilt {n : ℕ} {S K : Set (Fin n → ℝ)}
    (hb : Bornology.IsBounded S) (hSK : S ⊆ K)
    (g : (Fin n → ℝ) → ℝ) (ha : AnalyticOnNhd ℝ g K)
    (hp : ∀ y ∈ S, 0 < g y) (hz : ∀ y ∈ closure S \ S, g y = 0)
    {x : Fin n → ℝ} (hx : x ∈ S) (v : Fin n → ℝ) (hv : v ≠ 0) :
    ∃ h : (Fin n → ℝ) → ℝ, AnalyticOnNhd ℝ h K ∧
      (∀ y ∈ S, 0 < h y) ∧ (∀ y ∈ closure S \ S, h y = 0) ∧
      fderiv ℝ h x v ≠ 0 := by
  by_cases hgv : fderiv ℝ g x v ≠ 0
  · exact ⟨g, ha, hp, hz, hgv⟩
  · have hgv0 : fderiv ℝ g x v = 0 := not_ne_iff.mp hgv
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra! h
      exact hv (funext h)
    obtain ⟨R, _, hR⟩ := hb.exists_pos_norm_lt
    let a : (Fin n → ℝ) → ℝ := fun y => R + y i
    have haa (y : Fin n → ℝ) : AnalyticAt ℝ a y :=
      analyticAt_const.add ((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).analyticAt y)
    refine ⟨fun y => g y * a y, fun y hy => (ha y hy).mul (haa y), ?_, ?_, ?_⟩
    · intro y hy
      apply mul_pos (hp y hy)
      have hn : |y i| < R := (norm_le_pi_norm y i).trans_lt (hR y hy)
      have hl := (abs_lt.mp hn).1
      change 0 < R + y i
      linarith
    · intro y hy
      change g y * a y = 0
      rw [hz y hy, zero_mul]
    · rw [fderiv_fun_mul (ha x (hSK hx)).differentiableAt (haa x).differentiableAt]
      have had : fderiv ℝ a x v = v i := by
        change fderiv ℝ (fun y => R + (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) y) x v = v i
        rw [fderiv_fun_add (differentiableAt_const R)
          (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).differentiableAt,
          fderiv_const_apply, ContinuousLinearMap.fderiv, zero_add]
        rfl
      change g x * fderiv ℝ a x v + a x * fderiv ℝ g x v ≠ 0
      rw [had, hgv0, mul_zero, add_zero]
      exact mul_ne_zero (ne_of_gt (hp x hx)) hi

end PlanarNikodym
