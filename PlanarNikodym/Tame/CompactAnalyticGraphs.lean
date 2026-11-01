import PlanarNikodym.Tame.RestrictedAnalyticSets

noncomputable section
open Set Metric

namespace PlanarNikodym

/-- A germ of an actual analytic function has a definable graph on a
smaller ball. The proof normalizes that ball into the standard cube. -/
theorem exists_ranDefinableOn_ball_of_analyticAt {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} {c : Fin n → ℝ} (hf : AnalyticAt ℝ f c) :
    ∃ r : ℝ, 0 < r ∧ RanDefinableOn f (ball c r) := by
  obtain ⟨R, hR, hfa⟩ := hf.exists_ball_analyticOnNhd
  let r := R / 2
  have hr : 0 < r := by dsimp [r]; positivity
  let g : (Fin n → ℝ) → ℝ := fun u => f (c + r • u)
  have hg : AnalyticOnNhd ℝ g (restrictedAnalyticCube n) := by
    intro u hu
    have hball : c + r • u ∈ ball c R := by
      rw [mem_ball, dist_pi_lt_iff hR]
      intro i
      have hlow : -1 ≤ u i := hu.1 i
      have hupp : u i ≤ 1 := hu.2 i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Real.dist_eq]
      rw [abs_lt]
      dsimp [r] at *
      constructor <;> nlinarith
    have hlin : AnalyticAt ℝ (fun u : Fin n → ℝ => c + r • u) u :=
      analyticAt_const.add (analyticAt_id.const_smul (c := r))
    exact (hfa _ hball).comp (f := fun u : Fin n → ℝ => c + r • u) hlin
  let F : (Fin n → ℝ) → (Fin n → ℝ) := fun x => r⁻¹ • (x - c)
  have hF : RanDefinableMap F := by
    intro i
    exact ranDefinableFun_mul (ranDefinableFun_const r⁻¹)
      (ranDefinableFun_sub (ranDefinableFun_coordinate i) (ranDefinableFun_const (c i)))
  have hsub : ball c r ⊆ F ⁻¹' restrictedAnalyticCube n := by
    intro x hx
    have hdist := (dist_pi_lt_iff hr).mp hx
    constructor <;> intro i
    · have hi := (abs_lt.mp (hdist i)).1
      change -1 ≤ r⁻¹ * (x i - c i)
      rw [← div_eq_inv_mul, le_div_iff₀ hr]
      simpa only [Real.dist_eq, neg_one_mul] using le_of_lt hi
    · have hi := (abs_lt.mp (hdist i)).2
      change r⁻¹ * (x i - c i) ≤ 1
      rw [← div_eq_inv_mul, div_le_iff₀ hr]
      simpa only [one_mul] using le_of_lt hi
  refine ⟨r, hr, ?_⟩
  apply (((ranDefinableOn_restrictedAnalytic g hg).preimage_map hF).restrict
    (ranDefinable_ball c r) hsub).congr
  intro x _
  change f (c + r • (r⁻¹ • (x - c))) = f x
  rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul, add_sub_cancel]

/-- On a compact set of analytic germs one obtains finitely many genuine
definable graph patches on an open definable neighbourhood. -/
theorem exists_ranDefinableOn_nhds_of_compact {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hf : AnalyticOnNhd ℝ f K) :
    ∃ U : Set (Fin n → ℝ), IsOpen U ∧ K ⊆ U ∧
      RanDefinable U ∧ RanDefinableOn f U := by
  classical
  choose r hr hgraph using fun x : K => exists_ranDefinableOn_ball_of_analyticAt (hf x x.2)
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => ball x.1 (r x))
    (fun _ => isOpen_ball) (by intro x hx; exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr _)⟩)
  let U := ⋃ x : s, ball x.1.1 (r x.1)
  refine ⟨U, isOpen_iUnion (fun _ => isOpen_ball), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  · exact Set.definable_iUnion_of_finite (fun x : s => ranDefinable_ball x.1.1 (r x.1))
  · exact RanDefinableOn.finite_union (fun x : s => hgraph x.1)

theorem ranDefinableOn_of_analyticOnNhd_compact_closure {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} {S : Set (Fin n → ℝ)} (hS : RanDefinable S)
    (hc : IsCompact (closure S)) (hf : AnalyticOnNhd ℝ f (closure S)) :
    RanDefinableOn f S := by
  obtain ⟨U, _, hU, _, hfU⟩ := exists_ranDefinableOn_nhds_of_compact hc hf
  exact hfU.restrict hS (subset_closure.trans hU)

theorem ranDefinable_bounded_analytic_sublevel {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} {S : Set (Fin n → ℝ)}
    (hc : IsCompact (closure S)) (hf : AnalyticOnNhd ℝ f (closure S))
    (hS : S = {x | f x < 0}) : RanDefinable S := by
  obtain ⟨U, _, hU, _, hfU⟩ := exists_ranDefinableOn_nhds_of_compact hc hf
  have he : {x | x ∈ U ∧ f x < 0} = S := by
    ext x
    rw [hS]
    exact ⟨And.right, fun hx => ⟨hU (subset_closure (hS ▸ hx)), hx⟩⟩
  rw [← he]
  exact hfU.sublevel 0

end PlanarNikodym
