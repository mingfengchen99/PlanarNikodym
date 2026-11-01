import PlanarNikodym.Tame.FiniteSemianalyticCoordinates
import PlanarNikodym.Tame.FamilyStability
import PlanarNikodym.Geometry.FiniteComponentImages

/-! Actual finite definable components of the original analytic sublevel
seeds, transported to Family parameter coordinates and tame restrictions. -/
noncomputable section
open Set Metric
namespace PlanarNikodym

theorem finite_definable_components_of_analytic_sublevel_at_closure
    {ι : Type*} [Fintype ι] {A : Set (ι → ℝ)} {f : (ι → ℝ) → ℝ}
    (hf : AnalyticOnNhd ℝ f (closure A)) (hA : A = {x | f x < 0})
    (hb : Bornology.IsBounded A) :
    (componentDomains A).Finite ∧ ∀ x, RanDefinable (connectedComponentIn A x) := by
  apply finite_definable_components_of_analytic_signs_at_closure
    (fun _ : Fin 1 => f) (fun _ => hf) (fun s => s 0 = 0) _ hb
  intro x
  rw [hA]
  exact oneDimensionalSign_eq_zero.symm

theorem Family.ranTame_components_of_analytic_sublevel
    {d : ℕ} (G : Family 2 d) (hG : G.RanTame) (hb : Bornology.IsBounded G.W)
    (f : Parameters 2 d → ℝ) (hf : AnalyticOnNhd ℝ f (closure G.W))
    (hW : G.W = {p | f p < 0}) :
    (componentDomains G.W).Finite ∧
      ∀ p, (G.restrictTo (connectedComponentIn G.W p)).RanTame := by
  let E := ranParameterEquiv d
  let A := E ⁻¹' G.W
  have hcl : closure A = E ⁻¹' closure G.W := (E.toHomeomorph.preimage_closure G.W).symm
  have hfa : AnalyticOnNhd ℝ (f ∘ E) (closure A) := by
    intro x hx
    have hxW : E x ∈ closure G.W := by change x ∈ E ⁻¹' closure G.W; rwa [← hcl]
    exact (hf (E x) hxW).comp (f := E) (E.analyticAt x)
  have hbA : Bornology.IsBounded A := by
    have h := E.symm.lipschitz.isBounded_image hb
    have he : E.symm '' G.W = E ⁻¹' G.W := by
      ext x
      exact ⟨fun ⟨y, hy, he⟩ => he ▸ (by simpa only [mem_preimage, E.apply_symm_apply] using hy),
        fun hx => ⟨E x, hx, E.symm_apply_apply x⟩⟩
    rwa [he] at h
  have heA : A = {x | (f ∘ E) x < 0} := by
    change E ⁻¹' G.W = _
    rw [hW]
    rfl
  obtain ⟨hfinite, hdef⟩ := finite_definable_components_of_analytic_sublevel_at_closure hfa heA hbA
  refine ⟨components_finite_of_homeomorph_preimage E.toHomeomorph G.W hfinite, ?_⟩
  intro p
  apply hG.restrictTo _ (connectedComponentIn_subset G.W p)
  have he := preimage_connectedComponentIn_homeomorph E.toHomeomorph G.W p
  change RanDefinable (E.toHomeomorph ⁻¹' connectedComponentIn G.W p)
  rw [he]
  exact hdef (E.symm p)

/-- No component-definability certificate is supplied: it follows from the
actual analytic sublevel description of the seed. -/
theorem Family.ranTame_components_seed_sublevel
    {d : ℕ} (G : Family 2 d) (hb : Bornology.IsBounded G.W)
    (ha : G.IsAnalyticAtClosure) (f : Parameters 2 d → ℝ)
    (hf : AnalyticOnNhd ℝ f (closure G.W)) (hW : G.W = {p | f p < 0}) :
    (componentDomains G.W).Finite ∧
      ∀ p, (G.restrictTo (connectedComponentIn G.W p)).RanTame := by
  exact G.ranTame_components_of_analytic_sublevel
    (G.ranTame_of_definable_domain (ranDefinable_parameter_analytic_sublevel hb hf hW) hb ha)
    hb f hf hW

end PlanarNikodym
