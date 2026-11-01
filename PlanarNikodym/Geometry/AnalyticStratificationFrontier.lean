import PlanarNikodym.Geometry.AnalyticStratificationCylinders
import PlanarNikodym.Geometry.ContinuousPolynomialJets
import PlanarNikodym.Geometry.AnalyticSeparatingFrontier
import PlanarNikodym.Geometry.PolynomialThomFrontier

/-! The actual graph/band frontier comparison. A root graph retains one
fixed nonzero monic equation on its closure, excluding vertical bands even
over collision parameters. Over the same base, a different incident cell
has strictly smaller constructed chart dimension. -/
noncomputable section
open Set Polynomial
namespace PlanarNikodym

theorem analyticStrongSignCell_subset_closure_of_inter
    {X I : Type*} [TopologicalSpace X] (U : Set X) (g : I → X → ℝ)
    (s t : I → Fin 3)
    (hcl : closure (analyticStrongSignCell U g s) ∩ U = analyticWeakSignCell U g s)
    (hne : (analyticStrongSignCell U g t ∩ closure (analyticStrongSignCell U g s)).Nonempty) :
    analyticStrongSignCell U g t ⊆ closure (analyticStrongSignCell U g s) := by
  obtain ⟨z, hzT, hzCl⟩ := hne
  have hzWeak := (Set.ext_iff.mp hcl z).mp ⟨hzCl, hzT.1⟩
  intro y hy
  have hyWeak : y ∈ analyticWeakSignCell U g s := by
    refine ⟨hy.1, fun i => ?_⟩
    have hf : t i = 1 ∨ t i = s i := by
      simpa only [hzT.2 i] using (polynomialWeakSignCondition_iff _ _).mp (hzWeak.2 i)
    apply (polynomialWeakSignCondition_iff _ _).mpr
    exact hf.imp (fun he => (hy.2 i).trans he) (fun he => (hy.2 i).trans he)
  exact ((Set.ext_iff.mp hcl y).mpr hyWeak).1

theorem closure_analyticGraph_inter_base
    {E : Type*} [TopologicalSpace E] (C : Set E) (ρ : E → ℝ)
    (hρ : ∀ x ∈ C, ContinuousAt ρ x) :
    closure (analyticGraph C ρ) ∩ (C ×ˢ univ) = analyticGraph C ρ := by
  ext z
  constructor
  · rintro ⟨hz, hx, _⟩
    have hc : ContinuousAt (fun w : E × ℝ => w.2 - ρ w.1) z :=
      continuousAt_snd.sub (ContinuousAt.comp (f := Prod.fst) (g := ρ) (hρ z.1 hx) continuousAt_fst)
    have he : z.2 - ρ z.1 = 0 := hc.continuousWithinAt.eq_const_of_mem_closure hz
      (fun _ hw => sub_eq_zero.mpr hw.2)
    exact ⟨hx, sub_eq_zero.mp he⟩
  · intro hz
    exact ⟨subset_closure hz, hz.1, mem_univ _⟩

theorem closure_analyticBand_inter_base_subset
    {E : Type*} [TopologicalSpace E] (C : Set E) (l u : E → ℝ)
    (hl : ∀ x ∈ C, ContinuousAt l x) (hu : ∀ x ∈ C, ContinuousAt u x) :
    closure (analyticBand C l u) ∩ (C ×ˢ univ) ⊆
      {z | z.1 ∈ C ∧ l z.1 ≤ z.2 ∧ z.2 ≤ u z.1} := by
  rintro z ⟨hz, hx, _⟩
  have hcl := ContinuousAt.comp (f := Prod.fst) (g := l) (hl z.1 hx) continuousAt_fst
  have hcu := ContinuousAt.comp (f := Prod.fst) (g := u) (hu z.1 hx) continuousAt_fst
  exact ⟨hx,
    ContinuousWithinAt.closure_le hz hcl.continuousWithinAt continuousAt_snd.continuousWithinAt
      (fun _ hw => hw.2.1.le),
    ContinuousWithinAt.closure_le hz continuousAt_snd.continuousWithinAt hcu.continuousWithinAt
      (fun _ hw => hw.2.2.le)⟩

theorem exists_fixed_monic_equation_for_root_graph
    {E J : Type*} {m : J → ℕ} (a : (j : J) → E → Fin (m j) → ℝ)
    {C : Set E} (hC : C.Nonempty) (ρ : E → ℝ)
    (hroot : ∀ x ∈ C, ∃ j, (weierstrassPolynomial (a j x)).eval (ρ x) = 0)
    (hsign : ∀ j x, x ∈ C → ∀ y, y ∈ C →
      oneDimensionalSign ((weierstrassPolynomial (a j x)).eval (ρ x)) =
        oneDimensionalSign ((weierstrassPolynomial (a j y)).eval (ρ y))) :
    ∃ j, ∀ z ∈ analyticGraph C ρ, (weierstrassPolynomial (a j z.1)).eval z.2 = 0 := by
  obtain ⟨x, hx⟩ := hC
  obtain ⟨j, hj⟩ := hroot x hx
  refine ⟨j, fun z hz => ?_⟩
  rw [hz.2]
  apply oneDimensionalSign_eq_one.mp
  exact (hsign j z.1 hz.1 x hx).trans (oneDimensionalSign_eq_one.mpr hj)

theorem monic_zero_set_closure_not_contains_vertical_interval
    {E : Type*} [TopologicalSpace E] {m : ℕ} (a : E → Fin m → ℝ)
    (D : Set (E × ℝ)) (hzero : ∀ z ∈ D, (weierstrassPolynomial (a z.1)).eval z.2 = 0)
    (x : E) (ha : ContinuousAt a x) (l u : ℝ) (hlt : l < u) :
    ¬ ({x} ×ˢ Ioo l u ⊆ closure D) := by
  intro hsub
  have hz (t : ℝ) (ht : t ∈ Ioo l u) : (weierstrassPolynomial (a x)).eval t = 0 := by
    have hc : ContinuousAt (fun z : E × ℝ => (weierstrassPolynomial (a z.1)).eval z.2) (x, t) := by
      simpa only [Function.iterate_zero_apply] using
        continuousAt_joint_weierstrassPolynomial_iterate_derivative_eval a x t ha 0
    exact hc.continuousWithinAt.eq_const_of_mem_closure (hsub ⟨mem_singleton x, ht⟩) hzero
  exact (Set.Ioo_infinite hlt).not_finite
    ((Polynomial.finite_setOf_isRoot (weierstrassPolynomial_monic (a x)).ne_zero).subset hz)

theorem root_graph_closure_not_contains_vertical_interval
    {E J : Type*} [TopologicalSpace E] {m : J → ℕ}
    (a : (j : J) → E → Fin (m j) → ℝ)
    {C : Set E} (hC : C.Nonempty) (ρ : E → ℝ)
    (hroot : ∀ x ∈ C, ∃ j, (weierstrassPolynomial (a j x)).eval (ρ x) = 0)
    (hsign : ∀ j x, x ∈ C → ∀ y, y ∈ C →
      oneDimensionalSign ((weierstrassPolynomial (a j x)).eval (ρ x)) =
        oneDimensionalSign ((weierstrassPolynomial (a j y)).eval (ρ y)))
    (x : E) (ha : ∀ j, ContinuousAt (a j) x) (l u : ℝ) (hlt : l < u) :
    ¬ ({x} ×ˢ Ioo l u ⊆ closure (analyticGraph C ρ)) := by
  obtain ⟨j, hj⟩ := exists_fixed_monic_equation_for_root_graph a hC ρ hroot hsign
  exact monic_zero_set_closure_not_contains_vertical_interval (a j) (analyticGraph C ρ)
    hj x (ha j) l u hlt

theorem cylindrical_same_base_frontier_dimension
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (Q : AnalyticStratificationChart E) (c : Fin (n + 2) → E → ℝ)
    (ha : ∀ i, AnalyticOnNhd ℝ (c i) Q.image)
    (hc : ∀ x ∈ Q.image, StrictMono (fun i => c i x))
    (i j : Fin n ⊕ Fin (n + 1)) (hij : i ≠ j)
    (hne : ((Q.cylindrical c ha hc j).image ∩ closure (Q.cylindrical c ha hc i).image).Nonempty) :
    (Q.cylindrical c ha hc j).dim < (Q.cylindrical c ha hc i).dim := by
  obtain ⟨z, hzj, hzi⟩ := hne
  rw [AnalyticStratificationChart.cylindrical_image] at hzj hzi
  have hx : z.1 ∈ Q.image := mem_analyticCylindricalCell_fst hzj
  rcases i with i | i
  · have hzgraph : z ∈ analyticGraph Q.image (c i.castSucc.succ) :=
      (Set.ext_iff.mp (closure_analyticGraph_inter_base Q.image (c i.castSucc.succ)
        (fun x hx => (ha _ x hx).continuousAt)) z).mp ⟨hzi, hx, mem_univ _⟩
    exact False.elim (hij (analyticCylindricalCell_index_eq hc hzgraph hzj))
  · rcases j with j | j
    · simp only [AnalyticStratificationChart.cylindrical,
        AnalyticStratificationChart.graph_dim, AnalyticStratificationChart.band_dim]
      omega
    · have hb := closure_analyticBand_inter_base_subset Q.image (c i.castSucc) (c i.succ)
        (fun x hx => (ha _ x hx).continuousAt) (fun x hx => (ha _ x hx).continuousAt)
        ⟨hzi, hx, mem_univ _⟩
      have hneij : i ≠ j := fun he => hij (congrArg Sum.inr he)
      rcases lt_or_gt_of_ne hneij with hlt | hgt
      · have hord : c i.succ z.1 ≤ c j.castSucc z.1 :=
          (hc z.1 hx).monotone (by change (i : ℕ) + 1 ≤ (j : ℕ); exact hlt)
        exact False.elim (not_lt_of_ge hb.2.2 (hord.trans_lt hzj.2.1))
      · have hord : c j.succ z.1 ≤ c i.castSucc z.1 :=
          (hc z.1 hx).monotone (by change (j : ℕ) + 1 ≤ (i : ℕ); exact hgt)
        exact False.elim (not_lt_of_ge (hord.trans hb.2.1) hzj.2.2)

end PlanarNikodym
