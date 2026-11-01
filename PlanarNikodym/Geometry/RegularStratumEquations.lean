import PlanarNikodym.Geometry.AnalyticStratificationCharts
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Actual ambient regular equations for a stratum in a closed analytic
window. This proposition is an intermediate construction invariant; its
existence must be established by the graph/band induction. -/
noncomputable section
open Set Filter Module
open scoped Topology
namespace PlanarNikodym

def RegularStratumEquations {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K S : Set E) (k : ℕ) : Prop :=
  ∃ (c : ℕ) (F : E → Fin c → ℝ), c + k = finrank ℝ E ∧
    AnalyticOnNhd ℝ F K ∧ ∀ x ∈ S, F x = 0 ∧ Function.Surjective (fderiv ℝ F x)

namespace RegularStratumEquations
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mono {K S T : Set E} {k : ℕ} (h : RegularStratumEquations K S k)
    (hT : T ⊆ S) : RegularStratumEquations K T k := by
  obtain ⟨c, F, hc, ha, hF⟩ := h
  exact ⟨c, F, hc, ha, fun x hx => hF x (hT hx)⟩

/-- Full-dimensional open pieces need no equations, including dimension
zero; the derivative to the zero-dimensional target is surjective. -/
theorem full (K S : Set E) : RegularStratumEquations K S (finrank ℝ E) := by
  refine ⟨0, fun _ _ => 0, by omega, analyticOnNhd_const, ?_⟩
  intro x _
  refine ⟨rfl, ?_⟩
  intro y
  refine ⟨0, ?_⟩
  exact Subsingleton.elim _ _

theorem lift_band [FiniteDimensional ℝ E]
    {K S : Set E} {k : ℕ} (h : RegularStratumEquations K S k)
    (V A : Set (E × ℝ)) (hV : Prod.fst '' V ⊆ K) (hA : Prod.fst '' A ⊆ S)
    (hAV : A ⊆ V) :
    RegularStratumEquations V A (k + 1) := by
  obtain ⟨c, F, hc, ha, hF⟩ := h
  refine ⟨c, F ∘ Prod.fst, ?_, ?_, ?_⟩
  · rw [finrank_prod, finrank_self]
    omega
  · intro x hx
    exact (ha x.1 (hV (mem_image_of_mem _ hx))).comp analyticAt_fst
  · intro x hx
    have hbase := hF x.1 (hA (mem_image_of_mem _ hx))
    refine ⟨hbase.1, ?_⟩
    have hd := (ha x.1 (hV (mem_image_of_mem _ (hAV hx)))).differentiableAt
    rw [fderiv_comp x hd differentiableAt_fst]
    intro y
    obtain ⟨v, hv⟩ := hbase.2 y
    refine ⟨(v, 0), ?_⟩
    rw [fderiv_fst]
    exact hv

theorem lift_graph [FiniteDimensional ℝ E]
    {K S : Set E} {k : ℕ} (h : RegularStratumEquations K S k)
    (V A : Set (E × ℝ)) (hV : Prod.fst '' V ⊆ K) (hA : Prod.fst '' A ⊆ S)
    (hAV : A ⊆ V) (H : E × ℝ → ℝ) (hH : AnalyticOnNhd ℝ H V)
    (hzero : ∀ x ∈ A, H x = 0)
    (hvertical : ∀ x ∈ A, fderiv ℝ H x (0, 1) ≠ 0) :
    RegularStratumEquations V A k := by
  obtain ⟨c, F, hc, ha, hF⟩ := h
  let e := realCoordinateSplitEquiv (Fin.last c)
  let P : E × ℝ → (Fin c → ℝ) × ℝ := fun x => (F x.1, H x)
  have hPa : AnalyticOnNhd ℝ P V := fun x hx =>
    ((ha x.1 (hV (mem_image_of_mem _ hx))).comp analyticAt_fst).prod (hH x hx)
  refine ⟨c + 1, e ∘ P, ?_, fun x hx => (e.analyticAt _).comp (hPa x hx), ?_⟩
  · rw [finrank_prod, finrank_self]
    omega
  · intro x hx
    have hbase := hF x.1 (hA (mem_image_of_mem _ hx))
    refine ⟨?_, ?_⟩
    · change e (F x.1, H x) = 0
      rw [hbase.1, hzero x hx]
      exact e.map_zero
    · have hPd : HasFDerivAt P
          (((fderiv ℝ F x.1).comp (ContinuousLinearMap.fst ℝ E ℝ)).prod
            (fderiv ℝ H x)) x :=
        (((ha x.1 (hV (mem_image_of_mem _ (hAV hx)))).differentiableAt.hasFDerivAt.comp x
          hasFDerivAt_fst).prodMk (hH x (hAV hx)).differentiableAt.hasFDerivAt)
      change Function.Surjective (fderiv ℝ (e.toContinuousLinearMap ∘ P) x)
      rw [(e.toContinuousLinearMap.hasFDerivAt.comp x hPd).fderiv]
      intro y
      obtain ⟨v, hv⟩ := hbase.2 (e.symm y).1
      let B := fderiv ℝ H x
      let t := ((e.symm y).2 - B (v, 0)) / B (0, 1)
      have ht : B (v, t) = (e.symm y).2 := by
        have he : (v, t) = (v, 0) + t • (0, 1) := by ext <;> simp
        rw [he, map_add, map_smul]
        dsimp only [t, smul_eq_mul]
        rw [div_mul_cancel₀ _ (hvertical x hx)]
        ring
      refine ⟨(v, t), ?_⟩
      change e (fderiv ℝ F x.1 v, B (v, t)) = y
      rw [hv, ht, Prod.mk.eta, e.apply_symm_apply]

theorem transport {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K S : Set E} {k : ℕ} (h : RegularStratumEquations K S k) (hSK : S ⊆ K)
    (e : E ≃ₜ F) (hdim : finrank ℝ E = finrank ℝ F)
    (hei : ∀ y, AnalyticAt ℝ e.symm y)
    (hsi : ∀ y, Function.Surjective (fderiv ℝ e.symm y)) :
    RegularStratumEquations (e.symm ⁻¹' K) (e '' S) k := by
  obtain ⟨c, P, hc, ha, hP⟩ := h
  refine ⟨c, P ∘ e.symm, hc.trans hdim, fun y hy => (ha _ hy).comp (hei y), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxK := hSK hx
  constructor
  · simpa only [Function.comp_apply, e.symm_apply_apply] using (hP x hx).1
  · rw [fderiv_comp _ (by simpa only [e.symm_apply_apply] using (ha x hxK).differentiableAt)
      (hei (e x)).differentiableAt]
    intro y
    obtain ⟨v, hv⟩ := (hP x hx).2 y
    obtain ⟨w, hw⟩ := hsi (e x) v
    refine ⟨w, ?_⟩
    change fderiv ℝ P (e.symm (e x)) (fderiv ℝ e.symm (e x) w) = y
    rw [e.symm_apply_apply, hw, hv]

end RegularStratumEquations

theorem analytic_homeomorph_symm_fderiv_surjective
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃ₜ F) (he : ∀ x, AnalyticAt ℝ e x) (hi : ∀ y, AnalyticAt ℝ e.symm y)
    (y : F) : Function.Surjective (fderiv ℝ e.symm y) := by
  have hcomp := ((hi (e (e.symm y))).differentiableAt.hasFDerivAt.comp (e.symm y)
    (he (e.symm y)).differentiableAt.hasFDerivAt)
  have hcomp' : HasFDerivAt (e.symm ∘ e)
      ((fderiv ℝ e.symm y).comp (fderiv ℝ e (e.symm y))) (e.symm y) := by
    simpa only [e.apply_symm_apply] using hcomp
  have heq : e.symm ∘ e = id := funext e.symm_apply_apply
  rw [heq] at hcomp'
  have hid := hcomp'.unique (hasFDerivAt_id (𝕜 := ℝ) (e.symm y))
  intro v
  refine ⟨fderiv ℝ e (e.symm y) v, ?_⟩
  exact congrArg (fun L : E →L[ℝ] E => L v) hid

/-- Independent regular equations of the correct codimension identify the
actual derivative image of the existing chart, rather than a labelled
abstract tangent space. -/
theorem AnalyticStratificationChart.range_fderiv_eq_ker_of_equations
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : AnalyticStratificationChart E) (K : Set E) (hQK : Q.image ⊆ K)
    (c : ℕ) (F : E → Fin c → ℝ) (hc : c + Q.dim = finrank ℝ E)
    (ha : AnalyticOnNhd ℝ F K)
    (hF : ∀ x ∈ Q.image, F x = 0 ∧ Function.Surjective (fderiv ℝ F x))
    (q : Fin Q.dim → ℝ) (hq : q ∈ Q.source) :
    (fderiv ℝ Q.map q).toLinearMap.range = (fderiv ℝ F (Q.map q)).toLinearMap.ker := by
  have hqI : Q.map q ∈ Q.image := mem_image_of_mem _ hq
  have hsurj := (hF _ hqI).2
  have he : F ∘ Q.map =ᶠ[𝓝 q] fun _ => 0 := by
    filter_upwards [Q.open_source.mem_nhds hq] with x hx
    exact (hF _ (mem_image_of_mem _ hx)).1
  have hd : (fderiv ℝ F (Q.map q)).comp (fderiv ℝ Q.map q) = 0 := by
    rw [← fderiv_comp q (ha _ (hQK hqI)).differentiableAt
      (Q.analytic_map q hq).differentiableAt, he.fderiv_eq]
    exact fderiv_const_apply 0
  have hle : (fderiv ℝ Q.map q).toLinearMap.range ≤
      (fderiv ℝ F (Q.map q)).toLinearMap.ker := by
    rintro _ ⟨v, rfl⟩
    exact congrArg (fun L : (Fin Q.dim → ℝ) →L[ℝ] (Fin c → ℝ) => L v) hd
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hdim : finrank ℝ (fderiv ℝ Q.map q).toLinearMap.range = Q.dim := by
    simpa using LinearMap.finrank_range_of_inj (Q.derivative_injective q hq)
  have hrank := (fderiv ℝ F (Q.map q)).toLinearMap.finrank_range_add_finrank_ker
  have hr : (fderiv ℝ F (Q.map q)).toLinearMap.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  rw [hr, finrank_top, finrank_pi, Fintype.card_fin] at hrank
  omega


theorem AnalyticStratificationChart.regular_equations_tangent
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : AnalyticStratificationChart E) (K : Set E) (hQK : Q.image ⊆ K)
    (h : RegularStratumEquations K Q.image Q.dim) :
    ∃ (c : ℕ) (F : E → Fin c → ℝ), c + Q.dim = finrank ℝ E ∧
      AnalyticOnNhd ℝ F K ∧ (∀ x ∈ Q.image, F x = 0) ∧
      ∀ q ∈ Q.source, Function.Surjective (fderiv ℝ F (Q.map q)) ∧
        (fderiv ℝ Q.map q).toLinearMap.range = (fderiv ℝ F (Q.map q)).toLinearMap.ker := by
  obtain ⟨c, F, hc, ha, hF⟩ := h
  refine ⟨c, F, hc, ha, fun x hx => (hF x hx).1, ?_⟩
  intro q hq
  exact ⟨(hF _ (mem_image_of_mem _ hq)).2,
    Q.range_fderiv_eq_ker_of_equations K hQK c F hc ha hF q hq⟩

end PlanarNikodym
