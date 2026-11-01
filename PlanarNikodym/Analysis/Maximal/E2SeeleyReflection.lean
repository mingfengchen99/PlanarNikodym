import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.Topology

/-! Linear reflection/dilation in the time coordinate, preserving all
parameter coordinates and mapping one closed half space to the other. -/
noncomputable section
open Set
namespace PlanarNikodym
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

def e2PositiveHalfSpace : Set (ℝ × E) := Ici 0 ×ˢ univ
def e2NegativeHalfSpace : Set (ℝ × E) := Iic 0 ×ˢ univ

omit [NormedSpace ℝ E] in
theorem e2PositiveHalfSpace_isClosed : IsClosed (e2PositiveHalfSpace E) := isClosed_Ici.prod isClosed_univ
omit [NormedSpace ℝ E] in
theorem e2NegativeHalfSpace_isClosed : IsClosed (e2NegativeHalfSpace E) := isClosed_Iic.prod isClosed_univ
theorem e2PositiveHalfSpace_convex : Convex ℝ (e2PositiveHalfSpace E) := (convex_Ici 0).prod convex_univ
theorem e2NegativeHalfSpace_convex : Convex ℝ (e2NegativeHalfSpace E) := (convex_Iic 0).prod convex_univ

omit [NormedSpace ℝ E] in
theorem e2PositiveHalfSpace_closure_interior : closure (interior (e2PositiveHalfSpace E)) = e2PositiveHalfSpace E := by
  simp only [e2PositiveHalfSpace, interior_prod_eq, interior_Ici, interior_univ,
    closure_prod_eq, closure_Ioi, closure_univ]

omit [NormedSpace ℝ E] in
theorem e2NegativeHalfSpace_closure_interior : closure (interior (e2NegativeHalfSpace E)) = e2NegativeHalfSpace E := by
  simp only [e2NegativeHalfSpace, interior_prod_eq, interior_Iic, interior_univ,
    closure_prod_eq, closure_Iio, closure_univ]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem e2HalfSpaces_cover : e2PositiveHalfSpace E ∪ e2NegativeHalfSpace E = univ := by
  ext x
  simp only [e2PositiveHalfSpace, e2NegativeHalfSpace, mem_union, mem_prod, mem_Ici, mem_Iic,
    mem_univ, and_true, iff_true]
  exact le_total 0 x.1

def e2TimeDilation (b : ℝ) : (ℝ × E) →L[ℝ] (ℝ × E) :=
  (b • ContinuousLinearMap.fst ℝ ℝ E).prod (ContinuousLinearMap.snd ℝ ℝ E)

@[simp] theorem e2TimeDilation_apply (b : ℝ) (x : ℝ × E) : e2TimeDilation E b x = (b * x.1, x.2) := rfl

theorem e2TimeDilation_preimage_half {b : ℝ} (hb : b < 0) :
    (e2TimeDilation E b) ⁻¹' e2PositiveHalfSpace E = e2NegativeHalfSpace E := by
  ext x
  simp only [mem_preimage, e2PositiveHalfSpace, e2NegativeHalfSpace, mem_prod,
    mem_Ici, mem_Iic, mem_univ, and_true, e2TimeDilation_apply]
  constructor
  · intro hh
    by_contra hx
    exact not_lt_of_ge hh (mul_neg_of_neg_of_pos hb (lt_of_not_ge hx))
  · exact fun hh => mul_nonneg_of_nonpos_of_nonpos hb.le hh

theorem e2TimeDilation_norm_le {b : ℝ} (hb : 1 ≤ |b|) : ‖e2TimeDilation E b‖ ≤ |b| := by
  apply (e2TimeDilation E b).opNorm_le_bound (abs_nonneg b)
  intro x
  simp only [e2TimeDilation_apply, Prod.norm_def, norm_mul, Real.norm_eq_abs]
  apply max_le
  · exact mul_le_mul_of_nonneg_left (le_max_left _ _) (abs_nonneg _)
  · exact (le_max_right _ _).trans (le_mul_of_one_le_left (by positivity) hb)

end PlanarNikodym
