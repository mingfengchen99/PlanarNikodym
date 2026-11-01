import PlanarNikodym.Geometry.AnalyticSeparatingFrontier
import PlanarNikodym.Geometry.FixedStripThomFrontierTests
import PlanarNikodym.Geometry.AnalyticDerivativeEvaluation

/-! Actual polynomial dimension lifting for both connectedness and exact
relative weak-sign frontiers. The lower-dimensional frontiers are combined
with the proved compact-section Thom frontiers on a fixed vertical strip. -/
noncomputable section
open Set Metric Polynomial
namespace PlanarNikodym
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_polynomial_separating_frontier_lifting
    (H : LocalAnalyticSeparatingFrontier E)
    {J : Type} [Fintype J] (m : J → ℕ) (a : (j : J) → E → Fin (m j) → ℝ)
    (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r)
    (ha : ∀ j, AnalyticOnNhd ℝ (a j) (ball 0 ε)) :
    ∃ B : Set E, IsOpen B ∧ (0 : E) ∈ B ∧ B ⊆ ball 0 ε ∧
      ∃ (κ : Type) (_ : Fintype κ) (g : κ → E × ℝ → ℝ),
        (∀ k, AnalyticOnNhd ℝ (g k) (B ×ˢ Ioo (-r) r)) ∧
        (∀ j, ∃ k, ∀ z ∈ B ×ˢ Ioo (-r) r,
          g k z = (weierstrassPolynomial (a j z.1)).eval z.2) ∧
        ∀ s, analyticStrongSignCell (B ×ˢ Ioo (-r) r) g s = ∅ ∨
          (IsConnected (analyticStrongSignCell (B ×ˢ Ioo (-r) r) g s) ∧
            closure (analyticStrongSignCell (B ×ˢ Ioo (-r) r) g s) ∩ (B ×ˢ Ioo (-r) r) =
              analyticWeakSignCell (B ×ˢ Ioo (-r) r) g s) := by
  classical
  obtain ⟨δ, hδ, ι, hι, f, _, hf, hlift⟩ :=
    exists_fixedStrip_thom_frontier_tests m a (0 : E)
      (fun j => ha j 0 (mem_ball_self hε)) r hr
  obtain ⟨B, hB, h0B, hBsub, κ, hκ, b, hb, hinc, hfront⟩ :=
    H f 0 (fun i => hf i 0 (mem_ball_self hδ)) (ball 0 (min ε δ)) isOpen_ball
      (mem_ball_self (lt_min hε hδ))
  have hBε : B ⊆ ball 0 ε := hBsub.trans (ball_subset_ball (min_le_left _ _))
  have hBδ : B ⊆ ball 0 δ := hBsub.trans (ball_subset_ball (min_le_right _ _))
  let M := stripPolynomialDegree m
  let A := stripPolynomialCoefficients m a r
  let Q (x : E) := polynomialDerivativeFamily (fun j => weierstrassPolynomial (A j x)) M
  let g : κ ⊕ PolynomialDerivativeIndex M → E × ℝ → ℝ :=
    Sum.elim (fun k z => b k z.1) (fun q z => (Q z.1 q).eval z.2)
  have hA (j : J ⊕ Fin 2) (x : E) (hx : x ∈ B) : AnalyticAt ℝ (A j) x := by
    rcases j with j | i
    · exact ha j x (hBε hx)
    · exact analyticAt_const
  refine ⟨B, hB, h0B, hBε, κ ⊕ PolynomialDerivativeIndex M, inferInstance, g, ?_, ?_, ?_⟩
  · intro k z hz
    rcases k with k | q
    · exact AnalyticAt.comp (f := fun z : E × ℝ => z.1) (g := b k) (hb k z.1 hz.1) analyticAt_fst
    · exact analyticAt_joint_weierstrass_iterated_derivative_eval (A q.1) q.2.val z.1 z.2
        (hA q.1 z.1 hz.1)
  · intro j
    refine ⟨Sum.inr ⟨Sum.inl j, ⟨0, by dsimp [M, stripPolynomialDegree]; omega⟩⟩, ?_⟩
    intro z _
    rfl
  · intro s
    let t : κ → Fin 3 := fun k => s (Sum.inl k)
    let u : PolynomialDerivativeIndex M → Fin 3 := fun q => s (Sum.inr q)
    let C := analyticStrongSignCell B b t
    have he : analyticStrongSignCell (B ×ˢ Ioo (-r) r) g s =
        polynomialCylindricalSignCell C (-r) r Q u := by
      ext z
      constructor
      · intro hz
        exact ⟨⟨⟨hz.1.1, fun k => hz.2 (Sum.inl k)⟩, hz.1.2⟩, fun q => hz.2 (Sum.inr q)⟩
      · intro hz
        refine ⟨⟨hz.1.1.1, hz.1.2⟩, ?_⟩
        rintro (k | q)
        · exact hz.1.1.2 k
        · exact hz.2 q
    rcases hfront t with hempty | ⟨hC, hCcl⟩
    · left
      rw [he]
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      have hx : z.1 ∈ analyticStrongSignCell B b t := hz.1.1
      rw [hempty] at hx
      exact hx
    · have hCsub : C ⊆ ball 0 δ := fun _ hx => hBδ hx.1
      have hfs i x (hx : x ∈ C) y (hy : y ∈ C) :
          oneDimensionalSign (f i x) = oneDimensionalSign (f i y) := by
        obtain ⟨k, hk⟩ := hinc i
        rw [← hk hx.1, ← hk hy.1]
        exact (hx.2 k).trans (hy.2 k).symm
      rcases hlift C hCsub hC hfs u with hempty | ⟨hc, hPolyCl⟩
      · exact Or.inl (he.trans hempty)
      · right
        refine ⟨he.symm ▸ hc, ?_⟩
        rw [he]
        ext z
        constructor
        · rintro ⟨hzCl, hzW⟩
          have hw := (Set.ext_iff.mp hPolyCl z).mp ⟨hzCl, hBδ hzW.1, hzW.2⟩
          have hbWeak := (Set.ext_iff.mp hCcl z.1).mp ⟨hw.1.1, hzW.1⟩
          refine ⟨hzW, ?_⟩
          rintro (k | q)
          · exact hbWeak.2 k
          · exact hw.2.2 q
        · intro hz
          have hbWeak : z.1 ∈ analyticWeakSignCell B b t :=
            ⟨hz.1.1, fun k => hz.2 (Sum.inl k)⟩
          have hbCl := (Set.ext_iff.mp hCcl z.1).mpr hbWeak
          have hw : z ∈ {w : E × ℝ | w.1 ∈ closure C ∩ ball 0 δ ∧
              w.2 ∈ Ioo (-r) r ∧ w.2 ∈ polynomialThomFamilyCell true (Q w.1) u} :=
            ⟨⟨hbCl.1, hBδ hz.1.1⟩, hz.1.2, fun q => hz.2 (Sum.inr q)⟩
          exact ⟨((Set.ext_iff.mp hPolyCl z).mpr hw).1, hz.1⟩

end PlanarNikodym
