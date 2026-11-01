import PlanarNikodym.Geometry.SemianalyticBasicSets
import PlanarNikodym.Geometry.NonzeroDirectionFrame

/-! Genuine semianalyticity of the affine preparation cylinders used in
finite-dimensional analytic stratification. The coordinate map is actual. -/
noncomputable section
open Set
namespace PlanarNikodym

theorem LocallySemianalytic.finCylinder {n : ℕ} {B : Set (Fin n → ℝ)}
    (hB : LocallySemianalytic B) (A Z : ℝ) :
    LocallySemianalytic {w : Fin (n + 1) → ℝ | Fin.tail w ∈ B ∧ w 0 ∈ Ioo A Z} := by
  have hlo := locallySemianalytic_global_analytic_sublevel
    (fun w : Fin (n + 1) → ℝ => A - w 0)
    (fun w => analyticAt_const.sub (analyticAt_coordinate 0 w))
  have hhi := locallySemianalytic_global_analytic_sublevel
    (fun w : Fin (n + 1) → ℝ => w 0 - Z)
    (fun w => (analyticAt_coordinate 0 w).sub analyticAt_const)
  have hstrip : LocallySemianalytic {w : Fin (n + 1) → ℝ | w 0 ∈ Ioo A Z} := by
    convert hlo.inter hhi using 1
    ext w
    simp only [mem_inter_iff, mem_setOf_eq, mem_Ioo, sub_neg]
  exact (hB.preimage_analytic Fin.tail analyticAt_finTail).inter hstrip

@[simp] theorem realCoordinateSplitEquiv_zero_apply {n : ℕ} (z : (Fin n → ℝ) × ℝ) :
    realCoordinateSplitEquiv (0 : Fin (n + 1)) z = Fin.cons z.2 z.1 := by
  change Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) 0 z.2 z.1 = _
  exact Fin.insertNth_zero' _ _

theorem LocallySemianalytic.affineCylinderImage {n : ℕ} {B : Set (Fin n → ℝ)}
    (hB : LocallySemianalytic B)
    (e : ((Fin n → ℝ) × ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ))
    (x₀ : Fin (n + 1) → ℝ) (A Z : ℝ) :
    LocallySemianalytic ((fun z => x₀ + e z) '' (B ×ˢ Ioo A Z)) := by
  let F : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) :=
    fun y => realCoordinateSplitEquiv (0 : Fin (n + 1)) (e.symm (y - x₀))
  have hF (y : Fin (n + 1) → ℝ) : AnalyticAt ℝ F y :=
    ((realCoordinateSplitEquiv (0 : Fin (n + 1))).analyticAt _).comp
      ((e.symm.analyticAt _).comp (analyticAt_id.sub analyticAt_const))
  have he : (fun z => x₀ + e z) '' (B ×ˢ Ioo A Z) =
      F ⁻¹' {w : Fin (n + 1) → ℝ | Fin.tail w ∈ B ∧ w 0 ∈ Ioo A Z} := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change Fin.tail (F (x₀ + e z)) ∈ B ∧ F (x₀ + e z) 0 ∈ Ioo A Z
      have hcancel : e.symm (x₀ + e z - x₀) = z := by
        rw [add_sub_cancel_left, e.symm_apply_apply]
      simpa only [mem_prod, F, hcancel, realCoordinateSplitEquiv_zero_apply, Fin.tail_cons,
        Fin.cons_zero] using hz
    · intro hy
      let z := e.symm (y - x₀)
      have hz : z ∈ B ×ˢ Ioo A Z := by
        simpa only [mem_prod, z, mem_preimage, mem_setOf_eq, F, realCoordinateSplitEquiv_zero_apply,
          Fin.tail_cons, Fin.cons_zero] using hy
      refine ⟨z, hz, ?_⟩
      dsimp only [z]
      rw [e.apply_symm_apply, add_sub_cancel]
  rw [he]
  exact (hB.finCylinder A Z).preimage_analytic F hF

end PlanarNikodym
