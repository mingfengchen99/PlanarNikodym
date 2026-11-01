import PlanarNikodym.Geometry.AnalyticSignRefinement
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Topology.Algebra.Group.Basic

/-! Actual transport of finite analytic sign-separating extensions through
analytic changes of coordinates. The affine specialization constructs the
inverse analyticity from the continuous linear equivalence. -/
noncomputable section
open Set
namespace PlanarNikodym

theorem analyticStrongSignCell_preimage {X Y I : Type*}
    (e : X → Y) (U : Set Y) (f : I → Y → ℝ) (s : I → Fin 3) :
    analyticStrongSignCell (e ⁻¹' U) (fun i x => f i (e x)) s =
      e ⁻¹' analyticStrongSignCell U f s := rfl

theorem analyticStrongSignCell_connected_or_empty_homeomorph
    {X Y I : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (U : Set Y) (f : I → Y → ℝ)
    (h : ∀ s, analyticStrongSignCell U f s = ∅ ∨ IsConnected (analyticStrongSignCell U f s))
    (s : I → Fin 3) :
    analyticStrongSignCell (e ⁻¹' U) (fun i x => f i (e x)) s = ∅ ∨
      IsConnected (analyticStrongSignCell (e ⁻¹' U) (fun i x => f i (e x)) s) := by
  rw [analyticStrongSignCell_preimage]
  rcases h s with he | hc
  · exact Or.inl (by rw [he]; exact preimage_empty)
  · exact Or.inr (e.isConnected_preimage.mpr hc)

theorem exists_local_analytic_sign_refinement_homeomorph
    {E F I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃ₜ F) (x : E) (he : ∀ y : F, AnalyticAt ℝ e.symm y)
    (f : I → F → ℝ)
    (h : ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      ∃ (J : Type) (_ : Fintype J) (g : J → E → ℝ),
        (∀ q, AnalyticOnNhd ℝ (Sum.elim (fun i z => f i (e z)) g q) U) ∧
        ∀ s, analyticStrongSignCell U (Sum.elim (fun i z => f i (e z)) g) s = ∅ ∨
          IsConnected (analyticStrongSignCell U (Sum.elim (fun i z => f i (e z)) g) s)) :
    ∃ V : Set F, IsOpen V ∧ e x ∈ V ∧
      ∃ (J : Type) (_ : Fintype J) (g : J → F → ℝ),
        (∀ q, AnalyticOnNhd ℝ (Sum.elim f g q) V) ∧
        ∀ s, analyticStrongSignCell V (Sum.elim f g) s = ∅ ∨
          IsConnected (analyticStrongSignCell V (Sum.elim f g) s) := by
  obtain ⟨U, hU, hx, J, hJ, g, hg, hsep⟩ := h
  let g' : J → F → ℝ := fun j y => g j (e.symm y)
  have hfamily : Sum.elim f g' =
      fun q y => Sum.elim (fun i z => f i (e z)) g q (e.symm y) := by
    funext q y
    cases q <;> simp only [Sum.elim_inl, Sum.elim_inr, e.apply_symm_apply, g']
  refine ⟨e.symm ⁻¹' U, hU.preimage e.symm.continuous, by simpa using hx,
    J, hJ, g', ?_, ?_⟩
  · rw [hfamily]
    intro q y hy
    exact (hg q (e.symm y) hy).comp (he y)
  · rw [hfamily]
    exact analyticStrongSignCell_connected_or_empty_homeomorph e.symm U _ hsep

def analyticSignAffineCoordinates {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (x : F) : E ≃ₜ F :=
  e.toHomeomorph.trans (Homeomorph.addLeft x)

@[simp] theorem analyticSignAffineCoordinates_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (x : F) (z : E) :
    analyticSignAffineCoordinates e x z = x + e z := rfl

theorem analyticAt_analyticSignAffineCoordinates_symm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (x y : F) :
    AnalyticAt ℝ (analyticSignAffineCoordinates e x).symm y := by
  change AnalyticAt ℝ (fun z => e.symm (-x + z)) y
  exact (e.symm.analyticAt _).comp (analyticAt_const.add analyticAt_id)

theorem exists_local_analytic_sign_refinement_affine
    {E F I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (x : F) (f : I → F → ℝ)
    (h : ∃ U : Set E, IsOpen U ∧ (0 : E) ∈ U ∧
      ∃ (J : Type) (_ : Fintype J) (g : J → E → ℝ),
        (∀ q, AnalyticOnNhd ℝ (Sum.elim (fun i z => f i (x + e z)) g q) U) ∧
        ∀ s, analyticStrongSignCell U (Sum.elim (fun i z => f i (x + e z)) g) s = ∅ ∨
          IsConnected (analyticStrongSignCell U (Sum.elim (fun i z => f i (x + e z)) g) s)) :
    ∃ V : Set F, IsOpen V ∧ x ∈ V ∧
      ∃ (J : Type) (_ : Fintype J) (g : J → F → ℝ),
        (∀ q, AnalyticOnNhd ℝ (Sum.elim f g q) V) ∧
        ∀ s, analyticStrongSignCell V (Sum.elim f g) s = ∅ ∨
          IsConnected (analyticStrongSignCell V (Sum.elim f g) s) := by
  have htrans := exists_local_analytic_sign_refinement_homeomorph
    (analyticSignAffineCoordinates e x) 0
    (analyticAt_analyticSignAffineCoordinates_symm e x) f h
  simpa only [analyticSignAffineCoordinates_apply, map_zero, add_zero] using htrans

end PlanarNikodym
