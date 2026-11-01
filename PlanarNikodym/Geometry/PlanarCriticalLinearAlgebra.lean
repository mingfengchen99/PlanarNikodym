import PlanarNikodym.Core.Definitions
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Actual rank-deficient linear maps to the plane: kernel containment and
vanishing two-column minors. -/
noncomputable section
namespace PlanarNikodym

/-- A nonzero planar two-column minor gives actual surjectivity. -/
theorem planar_surjective_of_minor_ne_zero {n : ℕ}
    (L : Aux n →L[ℝ] Base 2) (v w : Aux n)
    (hdet : L v 0 * L w 1 - L v 1 * L w 0 ≠ 0) :
    Function.Surjective L := by
  intro y
  let d : ℝ := L v 0 * L w 1 - L v 1 * L w 0
  refine ⟨((y 0 * L w 1 - y 1 * L w 0) / d) • v +
    ((L v 0 * y 1 - L v 1 * y 0) / d) • w, ?_⟩
  ext i
  fin_cases i <;>
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;>
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div] <;>
    apply (div_eq_iff (show d ≠ 0 from hdet)).mpr <;> dsimp [d] <;> ring

/-- The actual failure of surjectivity to the plane is equivalent to the
vanishing of every two-column determinant. -/
theorem planar_not_surjective_iff_minors_zero {n : ℕ}
    (L : Aux n →L[ℝ] Base 2) :
    ¬ Function.Surjective L ↔
      ∀ v w, L v 0 * L w 1 - L v 1 * L w 0 = 0 := by
  constructor
  · intro h v w
    by_contra hdet
    exact h (planar_surjective_of_minor_ne_zero L v w hdet)
  · intro h hsurj
    obtain ⟨v, hv⟩ := hsurj (Pi.single (0 : Fin 2) 1)
    obtain ⟨w, hw⟩ := hsurj (Pi.single (1 : Fin 2) 1)
    have he := h v w
    rw [hv, hw] at he
    norm_num at he

/-- For a rank-deficient planar map with a nonzero first coordinate, its
first-coordinate kernel is contained in its second-coordinate kernel. -/
theorem planar_nonsurjective_kernel_inclusion {n : ℕ}
    (L : Aux n →L[ℝ] Base 2) (hL : ¬ Function.Surjective L)
    (h₀ : ∃ w, L w 0 ≠ 0) {v : Aux n} (hv : L v 0 = 0) :
    L v 1 = 0 := by
  obtain ⟨w, hw⟩ := h₀
  have h := (planar_not_surjective_iff_minors_zero L).mp hL v w
  rw [hv, zero_mul, zero_sub, neg_eq_zero] at h
  exact (mul_eq_zero.mp h).resolve_right hw

end PlanarNikodym
