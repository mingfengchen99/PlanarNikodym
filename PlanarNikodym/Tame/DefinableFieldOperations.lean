import PlanarNikodym.Tame.DefinableCalculus

/-! Field operations in the actual restricted analytic structure, including
division at zero. Local graph definability is preserved on the given domain. -/
noncomputable section
open Set
namespace PlanarNikodym

theorem ranDefinableFun_inv_any_index {ι : Type*} {f : (ι → ℝ) → ℝ}
    (hf : RanDefinableFun f) : RanDefinableFun (fun x => (f x)⁻¹) := by
  have h : RanDefinableFun (fun x : Fin 1 → ℝ => (x 0)⁻¹) :=
    ranDefinableFun_inv (ranDefinableFun_coordinate 0)
  exact h.comp (g := fun x _ => f x) (fun _ => hf)

theorem ranDefinableFun_div {ι : Type*} {f g : (ι → ℝ) → ℝ}
    (hf : RanDefinableFun f) (hg : RanDefinableFun g) :
    RanDefinableFun (fun x => f x / g x) := by
  simpa only [div_eq_mul_inv] using ranDefinableFun_mul hf (ranDefinableFun_inv_any_index hg)

theorem RanDefinableOn.add {ι : Type*} {f g : (ι → ℝ) → ℝ}
    {S : Set (ι → ℝ)} (hf : RanDefinableOn f S) (hg : RanDefinableOn g S)
    (hS : RanDefinable S) : RanDefinableOn (fun x => f x + g x) S := by
  apply ((ranDefinableFun_add (hf.zeroExtension hS)
    (hg.zeroExtension hS)).ranDefinableOn hS).congr
  intro x hx
  simp only [ranZeroExtension, if_pos hx]

theorem RanDefinableOn.mul {ι : Type*} {f g : (ι → ℝ) → ℝ}
    {S : Set (ι → ℝ)} (hf : RanDefinableOn f S) (hg : RanDefinableOn g S)
    (hS : RanDefinable S) : RanDefinableOn (fun x => f x * g x) S := by
  apply ((ranDefinableFun_mul (hf.zeroExtension hS)
    (hg.zeroExtension hS)).ranDefinableOn hS).congr
  intro x hx
  simp only [ranZeroExtension, if_pos hx]

theorem RanDefinableOn.neg {ι : Type*} {f : (ι → ℝ) → ℝ}
    {S : Set (ι → ℝ)} (hf : RanDefinableOn f S) (hS : RanDefinable S) :
    RanDefinableOn (fun x => -f x) S := by
  apply ((ranDefinableFun_neg (hf.zeroExtension hS)).ranDefinableOn hS).congr
  intro x hx
  simp only [ranZeroExtension, if_pos hx]

theorem RanDefinableOn.div {ι : Type*} {f g : (ι → ℝ) → ℝ}
    {S : Set (ι → ℝ)} (hf : RanDefinableOn f S) (hg : RanDefinableOn g S)
    (hS : RanDefinable S) : RanDefinableOn (fun x => f x / g x) S := by
  apply ((ranDefinableFun_div (hf.zeroExtension hS)
    (hg.zeroExtension hS)).ranDefinableOn hS).congr
  intro x hx
  simp only [ranZeroExtension, if_pos hx]

theorem RanDefinableOn.zeroSet {ι : Type*} {f : (ι → ℝ) → ℝ}
    {S : Set (ι → ℝ)} (hf : RanDefinableOn f S) (hS : RanDefinable S) :
    RanDefinable {x | x ∈ S ∧ f x = 0} := by
  convert hS.inter ((hf.zeroExtension hS).setOf_eq (ranDefinableFun_const 0)) using 1
  ext x
  by_cases hx : x ∈ S <;> simp [ranZeroExtension, hx]

theorem RanDefinableOn.nonzeroSet {ι : Type*} {f : (ι → ℝ) → ℝ}
    {S : Set (ι → ℝ)} (hf : RanDefinableOn f S) (hS : RanDefinable S) :
    RanDefinable {x | x ∈ S ∧ f x ≠ 0} := by
  convert hS.inter (hf.zeroSet hS).compl using 1
  ext x
  simp only [mem_setOf_eq, mem_inter_iff, mem_compl_iff]
  tauto

end PlanarNikodym
