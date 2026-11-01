import PlanarNikodym.Tame.DefinableAnalyticSignSets
import PlanarNikodym.Geometry.SemianalyticComponentUnions

/-! Bounded genuinely semianalytic sets and all their actual components
are R_an definable. Finite formulas are assembled on the compact closure;
no general o-minimality or component-definability input is supplied. -/
noncomputable section
open Set Metric
namespace PlanarNikodym

theorem LocallySemianalytic.exists_definable_ball_inter
    {n : ℕ} {A : Set (Fin n → ℝ)} (hA : LocallySemianalytic A) (x : Fin n → ℝ) :
    ∃ r : ℝ, 0 < r ∧ RanDefinable (A ∩ ball x r) := by
  obtain ⟨O, hO, hxO, J, hJ, f, hf, Q, hrep⟩ := hA x
  obtain ⟨r, hr, hsub, hgraph⟩ := exists_common_ranDefinableOn_ball_of_analytic_germs
    f x (fun j => hf j x hxO) O hO hxO
  refine ⟨r, hr, ?_⟩
  convert ranDefinableOn_boolean_sign_set (ranDefinable_ball x r) f hgraph Q using 1
  ext y
  exact ⟨fun hy => ⟨hy.2, (hrep y (hsub hy.2)).mp hy.1⟩,
    fun hy => ⟨(hrep y (hsub hy.1)).mpr hy.2, hy.1⟩⟩

theorem LocallySemianalytic.ranDefinable_of_compact_closure
    {n : ℕ} {A : Set (Fin n → ℝ)} (hA : LocallySemianalytic A)
    (hcompact : IsCompact (closure A)) : RanDefinable A := by
  classical
  choose r hr hd using fun x : closure A => hA.exists_definable_ball_inter x
  obtain ⟨s, hs⟩ := hcompact.elim_finite_subcover
    (fun x : closure A => ball x.val (r x)) (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr _)⟩)
  have he : A = ⋃ x : s, A ∩ ball x.val.val (r x.val) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hxs, hyball⟩ := mem_iUnion₂.mp (hs (subset_closure hy))
      exact mem_iUnion.mpr ⟨⟨x, hxs⟩, hy, hyball⟩
    · intro hy
      obtain ⟨x, hx⟩ := mem_iUnion.mp hy
      exact hx.1
  rw [he]
  exact Set.definable_iUnion_of_finite (fun x : s => hd x.val)

theorem LocallySemianalytic.ranDefinable_of_bounded
    {n : ℕ} {A : Set (Fin n → ℝ)} (hA : LocallySemianalytic A)
    (hb : Bornology.IsBounded A) : RanDefinable A :=
  hA.ranDefinable_of_compact_closure hb.isCompact_closure

theorem LocallySemianalytic.ranDefinable_componentDomain
    {n : ℕ} {A C : Set (Fin n → ℝ)} (hA : LocallySemianalytic A)
    (hb : Bornology.IsBounded A) (hC : C ∈ componentDomains A) : RanDefinable C := by
  have hsemi := hA.componentDomain hC
  obtain ⟨x, _, hxC⟩ := hC
  apply hsemi.ranDefinable_of_bounded
  exact hb.subset (by rw [hxC]; exact connectedComponentIn_subset A x)

theorem LocallySemianalytic.ranDefinable_connectedComponentIn
    {n : ℕ} {A : Set (Fin n → ℝ)} (hA : LocallySemianalytic A)
    (hb : Bornology.IsBounded A) (x : Fin n → ℝ) :
    RanDefinable (_root_.connectedComponentIn A x) :=
  (hA.connectedComponentIn x).ranDefinable_of_bounded (hb.subset (connectedComponentIn_subset A x))

theorem LocallySemianalytic.finite_definable_components_of_bounded
    {n : ℕ} {A : Set (Fin n → ℝ)} (hA : LocallySemianalytic A)
    (hb : Bornology.IsBounded A) :
    (componentDomains A).Finite ∧ ∀ C ∈ componentDomains A, RanDefinable C :=
  ⟨hA.components_finite_of_bounded hb, fun _ hC => hA.ranDefinable_componentDomain hb hC⟩

end PlanarNikodym
