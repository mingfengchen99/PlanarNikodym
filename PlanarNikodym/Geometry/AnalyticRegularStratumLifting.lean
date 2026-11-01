import PlanarNikodym.Geometry.AnalyticRegularRefinement
import PlanarNikodym.Geometry.AnalyticStratificationFixedStrip
import PlanarNikodym.Geometry.FixedStripThomFrontierTests
import PlanarNikodym.Geometry.AnalyticDerivativeEvaluation

/-! Polynomial dimension lifting with actual analytic stratum charts and
exact weak-sign frontiers. Both finite test families are constructed from
the original coefficients and supplied to the lower-dimensional induction. -/
noncomputable section
open Set Metric Polynomial
namespace PlanarNikodym
variable {d : ℕ}
local notation "E" => (Fin d → ℝ)

theorem exists_polynomial_regular_stratum_lifting
    (H : LocalAnalyticRegularRefinement d)
    {J : Type} [Fintype J] (m : J → ℕ) (a : (j : J) → E → Fin (m j) → ℝ)
    (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r)
    (ha : ∀ j, AnalyticOnNhd ℝ (a j) (ball 0 ε)) :
    ∃ B : Set E, IsOpen B ∧ (0 : E) ∈ B ∧ closure B ⊆ ball 0 ε ∧ LocallySemianalytic B ∧
      ∃ (κ : Type) (_ : Fintype κ) (g : κ → E × ℝ → ℝ) (η : (κ → Fin 3) → ℕ),
        (∀ k, AnalyticOnNhd ℝ (g k) (closure (B ×ˢ Ioo (-r) r))) ∧
        (∀ j, ∃ k, ∀ z ∈ B ×ˢ Ioo (-r) r,
          g k z = (weierstrassPolynomial (a j z.1)).eval z.2) ∧
        AnalyticDimensionedSignCells (B ×ˢ Ioo (-r) r) g η ∧
        AnalyticRegularSignCells (B ×ˢ Ioo (-r) r) g η := by
  classical
  obtain ⟨δ₀, hδ₀, ι₀, hι₀, f₀, hf₀, hchart⟩ :=
    exists_fixedStrip_analytic_derivative_thom_chart_tests m a (0 : E)
      (fun j => ha j 0 (mem_ball_self hε)) r hr
  obtain ⟨δ₁, hδ₁, ι₁, hι₁, f₁, _, hf₁, hfrontier⟩ :=
    exists_fixedStrip_thom_frontier_tests m a (0 : E)
      (fun j => ha j 0 (mem_ball_self hε)) r hr
  let δ := min δ₀ δ₁
  let f : ι₀ ⊕ ι₁ → E → ℝ := Sum.elim f₀ f₁
  have hf (i : ι₀ ⊕ ι₁) : AnalyticAt ℝ (f i) 0 := by
    rcases i with i | i
    · exact hf₀ i 0 (mem_ball_self hδ₀)
    · exact hf₁ i 0 (mem_ball_self hδ₁)
  obtain ⟨B, hB, h0B, hBsub, hBsemi, κ, hκ, b, η, hb, hinc, hbase, hregular⟩ :=
    H f 0 hf (ball 0 (min ε δ)) isOpen_ball (mem_ball_self (lt_min hε (lt_min hδ₀ hδ₁)))
  have hBcε : closure B ⊆ ball 0 ε := hBsub.trans (ball_subset_ball (min_le_left _ _))
  have hBε : B ⊆ ball 0 ε := subset_closure.trans hBcε
  have hBδ : B ⊆ ball 0 δ := subset_closure.trans (hBsub.trans (ball_subset_ball (min_le_right _ _)))
  have hBδ₀ : B ⊆ ball 0 δ₀ := hBδ.trans (ball_subset_ball (min_le_left _ _))
  have hBδ₁ : B ⊆ ball 0 δ₁ := hBδ.trans (ball_subset_ball (min_le_right _ _))
  let M := stripPolynomialDegree m
  let A := stripPolynomialCoefficients m a r
  let Q (x : E) := polynomialDerivativeFamily (fun j => weierstrassPolynomial (A j x)) M
  let g : κ ⊕ PolynomialDerivativeIndex M → E × ℝ → ℝ :=
    Sum.elim (fun k z => b k z.1) (fun q z => (Q z.1 q).eval z.2)
  let η' : (κ ⊕ PolynomialDerivativeIndex M → Fin 3) → ℕ := fun s =>
    η (fun k => s (Sum.inl k)) + monicDerivativeSignDimensionBit M (fun q => s (Sum.inr q))
  have hA (j : J ⊕ Fin 2) (x : E) (hx : x ∈ closure B) : AnalyticAt ℝ (A j) x := by
    rcases j with j | i
    · exact ha j x (hBcε hx)
    · exact analyticAt_const
  refine ⟨B, hB, h0B, hBcε, hBsemi, κ ⊕ PolynomialDerivativeIndex M, inferInstance, g, η', ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro k z hz
    have hzB : z.1 ∈ closure B := by
      rw [closure_prod_eq] at hz
      exact hz.1
    rcases k with k | q
    · exact AnalyticAt.comp (f := fun z : E × ℝ => z.1) (g := b k) (hb k z.1 hzB) analyticAt_fst
    · exact analyticAt_joint_weierstrass_iterated_derivative_eval (A q.1) q.2.val z.1 z.2
        (hA q.1 z.1 hzB)
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
    rcases hbase.1 t with hempty | ⟨T, hTC, hTdim, hCcl⟩
    · left
      rw [he]
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      have hx : z.1 ∈ analyticStrongSignCell B b t := hz.1.1
      rw [hempty] at hx
      exact hx
    · have hTC' : T.image = C := hTC
      have hC : IsConnected C := by rw [← hTC']; exact T.connected_image
      have hfs i x (hx : x ∈ C) y (hy : y ∈ C) :
          oneDimensionalSign (f i x) = oneDimensionalSign (f i y) := by
        obtain ⟨k, hk⟩ := hinc i
        rw [← hk hx.1, ← hk hy.1]
        exact (hx.2 k).trans (hy.2 k).symm
      have hTsub : T.image ⊆ ball 0 δ₀ := by rw [hTC]; exact fun _ hx => hBδ₀ hx.1
      have hTs i x (hx : x ∈ T.image) y (hy : y ∈ T.image) :
          oneDimensionalSign (f₀ i x) = oneDimensionalSign (f₀ i y) :=
        hfs (Sum.inl i) x (hTC' ▸ hx) y (hTC' ▸ hy)
      have hout := hchart T hTsub hTs u
      rw [hTC] at hout
      rcases hout with hempty | ⟨P, hP, _, _, hPdim⟩
      · exact Or.inl (he.trans hempty)
      · have hCsub : C ⊆ ball 0 δ₁ := fun _ hx => hBδ₁ hx.1
        rcases hfrontier C hCsub hC (fun i => hfs (Sum.inr i)) u with hempty | ⟨_, hPolyCl⟩
        · exact False.elim (P.connected_image.nonempty.ne_empty (hP.trans hempty))
        · right
          refine ⟨P, hP.trans he.symm, ?_, ?_⟩
          · dsimp only [η']
            rw [hPdim, hTdim]
          · rw [he]
            ext z
            constructor
            · rintro ⟨hzCl, hzW⟩
              have hw := (Set.ext_iff.mp hPolyCl z).mp ⟨hzCl, hBδ₁ hzW.1, hzW.2⟩
              have hbWeak := (Set.ext_iff.mp hCcl z.1).mp ⟨hw.1.1, hzW.1⟩
              refine ⟨hzW, ?_⟩
              rintro (k | q)
              · exact hbWeak.2 k
              · exact hw.2.2 q
            · intro hz
              have hbWeak : z.1 ∈ analyticWeakSignCell B b t :=
                ⟨hz.1.1, fun k => hz.2 (Sum.inl k)⟩
              have hbCl := (Set.ext_iff.mp hCcl z.1).mpr hbWeak
              have hw : z ∈ {w : E × ℝ | w.1 ∈ closure C ∩ ball 0 δ₁ ∧
                  w.2 ∈ Ioo (-r) r ∧ w.2 ∈ polynomialThomFamilyCell true (Q w.1) u} :=
                ⟨⟨hbCl.1, hBδ₁ hz.1.1⟩, hz.1.2, fun q => hz.2 (Sum.inr q)⟩
              exact ⟨((Set.ext_iff.mp hPolyCl z).mpr hw).1, hz.1⟩

  · intro s t hst hs ht hface
    let bs : κ → Fin 3 := fun k => s (Sum.inl k)
    let bt : κ → Fin 3 := fun k => t (Sum.inl k)
    let us : PolynomialDerivativeIndex M → Fin 3 := fun q => s (Sum.inr q)
    let ut : PolynomialDerivativeIndex M → Fin 3 := fun q => t (Sum.inr q)
    have hsB : (analyticStrongSignCell B b bs).Nonempty := by
      obtain ⟨z, hz⟩ := hs
      exact ⟨z.1, hz.1.1, fun k => hz.2 (Sum.inl k)⟩
    have htB : (analyticStrongSignCell B b bt).Nonempty := by
      obtain ⟨z, hz⟩ := ht
      exact ⟨z.1, hz.1.1, fun k => hz.2 (Sum.inl k)⟩
    have hBit := monicDerivativeSignDimensionBit_mono_of_face M us ut (fun q => hface (Sum.inr q))
    change η bt + monicDerivativeSignDimensionBit M ut < η bs + monicDerivativeSignDimensionBit M us
    by_cases hbt : bs = bt
    · obtain ⟨z, hzT⟩ := ht
      have hxB : z.1 ∈ analyticStrongSignCell B b bs := by
        rw [hbt]
        exact ⟨hzT.1.1, fun k => hzT.2 (Sum.inl k)⟩
      obtain ⟨T, hTC, _, _⟩ := (hbase.1 bs).resolve_left hsB.ne_empty
      have hTsub : T.image ⊆ ball 0 δ₀ := by rw [hTC]; exact fun _ hx => hBδ₀ hx.1
      have hTs i x (hx : x ∈ T.image) y (hy : y ∈ T.image) :
          oneDimensionalSign (f₀ i x) = oneDimensionalSign (f₀ i y) := by
        have hxC := (Set.ext_iff.mp hTC x).mp hx
        have hyC := (Set.ext_iff.mp hTC y).mp hy
        obtain ⟨k, hk⟩ := hinc (Sum.inl i)
        change oneDimensionalSign (f (Sum.inl i) x) = oneDimensionalSign (f (Sum.inl i) y)
        rw [← hk hxC.1, ← hk hyC.1]
        exact (hxC.2 k).trans (hyC.2 k).symm
      have hPolyNE : (polynomialCylindricalSignCell T.image (-r) r Q us).Nonempty := by
        obtain ⟨w, hw⟩ := hs
        have hwB : w.1 ∈ analyticStrongSignCell B b bs := ⟨hw.1.1, fun k => hw.2 (Sum.inl k)⟩
        exact ⟨w, ⟨⟨(Set.ext_iff.mp hTC w.1).mpr hwB, hw.1.2⟩, fun q => hw.2 (Sum.inr q)⟩⟩
      obtain ⟨_, _, _, hfiber, _⟩ := (hchart T hTsub hTs us).resolve_left hPolyNE.ne_empty
      obtain ⟨v, hv⟩ := hfiber z.1 ((Set.ext_iff.mp hTC z.1).mpr hxB)
      have hune : us ≠ ut := by
        intro he
        apply hst
        funext q
        rcases q with k | q
        · exact congrFun hbt k
        · exact congrFun he q
      have hstrict := monicDerivativeSignDimensionBit_strict_of_face M A z.1 us ut
        ⟨v, hv.2⟩ ⟨z.2, fun q => hzT.2 (Sum.inr q)⟩ (fun q => hface (Sum.inr q)) hune
      rw [hbt]
      omega
    · have hdim := hbase.2 bs bt hbt hsB htB (fun k => hface (Sum.inl k))
      omega


  · intro s hne
    let t : κ → Fin 3 := fun k => s (Sum.inl k)
    let v : PolynomialDerivativeIndex M → Fin 3 := fun q => s (Sum.inr q)
    let C := analyticStrongSignCell B b t
    have heq : analyticStrongSignCell (B ×ˢ Ioo (-r) r) g s =
        polynomialCylindricalSignCell C (-r) r Q v := by
      ext z
      constructor
      · intro hz
        exact ⟨⟨⟨hz.1.1, fun k => hz.2 (Sum.inl k)⟩, hz.1.2⟩, fun q => hz.2 (Sum.inr q)⟩
      · intro hz
        refine ⟨⟨hz.1.1.1, hz.1.2⟩, ?_⟩
        rintro (k | q)
        · exact hz.1.1.2 k
        · exact hz.2 q
    have hCne : C.Nonempty := by
      obtain ⟨z, hz⟩ := hne
      exact ⟨z.1, hz.1.1, fun k => hz.2 (Sum.inl k)⟩
    have hn := regular_equations_polynomial_thom_cell M A B C
      (fun _ hx => hx.1) (η t) (hregular t hCne) hA (-r) r v
    rw [heq] at hne ⊢
    exact hn hne

end PlanarNikodym
