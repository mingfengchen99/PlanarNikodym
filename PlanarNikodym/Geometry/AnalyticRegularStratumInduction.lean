import PlanarNikodym.Geometry.AnalyticConnectedSeparationPreparation
import PlanarNikodym.Geometry.AnalyticRegularStratumLifting

/-! Full dimension induction for actual analytic sign strata, with coherent
dimensions and strict frontier dimension decrease. -/
noncomputable section
open Set Metric Polynomial
namespace PlanarNikodym

theorem localAnalyticRegularRefinement_of_subsingleton
    (d : ℕ) [Subsingleton (Fin d → ℝ)] :
    LocalAnalyticRegularRefinement d := by
  let E := Fin d → ℝ
  intro J _ f x₀ ha O _ hxO
  have hf (j : J) : AnalyticOnNhd ℝ (f j) univ := by
    intro y _
    have hy : y = x₀ := Subsingleton.elim _ _
    exact hy ▸ ha j
  refine ⟨univ, isOpen_univ, mem_univ _, ?_, ?_, J, inferInstance, f, (fun _ => 0), (by simpa only [closure_univ] using hf), ?_, ⟨?_, ?_⟩, ?_⟩
  · intro y _
    have hy : y = x₀ := Subsingleton.elim _ _
    exact hy ▸ hxO
  · intro x
    exact ⟨univ, isOpen_univ, mem_univ _, Empty, inferInstance, Empty.elim,
      (fun j => Empty.elim j), (fun _ => True), fun _ _ => iff_true_intro (mem_univ _)⟩
  · exact fun j => ⟨j, fun _ _ => rfl⟩
  · intro s
    rcases (analyticStrongSignCell univ f s).eq_empty_or_nonempty with he | hne
    · exact Or.inl he
    · right
      refine ⟨AnalyticStratificationChart.point x₀, ?_, rfl, Set.Subset.antisymm ?_ ?_⟩
      · rw [AnalyticStratificationChart.point_image]
        ext y
        constructor
        · intro _
          obtain ⟨a, haS⟩ := hne
          have he : a = y := Subsingleton.elim _ _
          exact he ▸ haS
        · intro _
          exact Subsingleton.elim y x₀
      · exact closure_analyticStrongSignCell_inter_subset_weak univ isOpen_univ f
          (fun j => (hf j).continuousOn) s
      · intro x _
        obtain ⟨a, haS⟩ := hne
        have he : a = x := Subsingleton.elim _ _
        exact ⟨subset_closure (he ▸ haS), mem_univ _⟩
  · intro s t hst hs ht _
    obtain ⟨a, haS⟩ := hs
    obtain ⟨b, hbT⟩ := ht
    have he : a = b := Subsingleton.elim _ _
    have hab : s = t := by
      funext j
      have ha' : oneDimensionalSign (f j b) = s j := by rw [← he]; exact haS.2 j
      exact ha'.symm.trans (hbT.2 j)
    exact False.elim (hst hab)
  · intro s _
    simpa only [Module.finrank_zero_of_subsingleton] using
      (RegularStratumEquations.full (closure (univ : Set E)) (analyticStrongSignCell univ f s))

theorem localAnalyticRegularRefinement_succ (d : ℕ)
    (H : LocalAnalyticRegularRefinement d) :
    LocalAnalyticRegularRefinement (d + 1) := by
  classical
  intro J _ f x₀ ha O hO hxO
  obtain ⟨e, ε, r, hε, hr, hdomain, hf, hprep⟩ :=
    exists_localized_finite_analytic_germ_preparation f x₀ ha O hO hxO
  let D : Set ((Fin d → ℝ) × ℝ) := ball 0 ε ×ˢ Ioo (-r) r
  let F : J → ((Fin d → ℝ) × ℝ) → ℝ := fun j z => f j (x₀ + e z)
  let K := {j : J // ¬ ∀ z ∈ D, F j z = 0}
  have hprepared (k : K) :
      ∃ (m : ℕ) (a : (Fin d → ℝ) → Fin m → ℝ) (u : ((Fin d → ℝ) × ℝ) → ℝ),
        AnalyticOnNhd ℝ a (ball 0 ε) ∧ (∀ z ∈ D, u z ≠ 0) ∧
        ∀ z ∈ D, F k z = (weierstrassPolynomial (a z.1)).eval z.2 * u z := by
    rcases hprep k with hz | hp
    · exact False.elim (k.property hz)
    · exact hp
  choose m a u ha' hun hfactor using hprepared
  obtain ⟨B, hB, h0B, hBcε, hBsemi, κ, hκ, g, η, hg, hinc, hfront, hregular⟩ :=
    exists_polynomial_regular_stratum_lifting H m a (ε / 2) (r / 2)
      (by positivity) (by positivity) (fun k => (ha' k).mono (ball_subset_ball (by linarith)))
  let W : Set ((Fin d → ℝ) × ℝ) := B ×ˢ Ioo (-(r / 2)) (r / 2)
  have hclosedWD : closure W ⊆ D := by
    intro z hz
    rw [closure_prod_eq, closure_Ioo (by linarith : -(r / 2) ≠ r / 2)] at hz
    refine ⟨?_, ?_⟩
    · exact (ball_subset_ball (by linarith : ε / 2 ≤ ε)) (hBcε hz.1)
    · exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hWD : W ⊆ D := subset_closure.trans hclosedWD
  have hW : IsOpen W := hB.prod isOpen_Ioo
  have h0W : (0 : (Fin d → ℝ) × ℝ) ∈ W := ⟨h0B, by dsimp; constructor <;> linarith⟩
  have hF (j : J) : AnalyticOnNhd ℝ (F j) W := fun z hz => hf j z (hWD hz)
  have hzero (j : J) : (∀ z ∈ W, F j z = 0) ∨
      ∃ k : κ, ∀ z ∈ W, F j z = 0 ↔ g k z = 0 := by
    by_cases hj : ∀ z ∈ D, F j z = 0
    · exact Or.inl (fun z hz => hj z (hWD hz))
    · right
      let k : K := ⟨j, hj⟩
      obtain ⟨l, hl⟩ := hinc k
      refine ⟨l, fun z hz => ?_⟩
      have he := hfactor k z (hWD hz)
      change F j z = (weierstrassPolynomial (a k z.1)).eval z.2 * u k z at he
      rw [he, hl z hz, mul_eq_zero]
      simp [hun k z (hWD hz)]
  have hsumA (q : J ⊕ κ) : AnalyticOnNhd ℝ (Sum.elim F g q) (closure W) := by
    rcases q with j | k
    · exact fun z hz => hf j z (hclosedWD hz)
    · exact hg k
  have hsep : AnalyticDimensionedSignCells W (Sum.elim F g)
      (fun s => η (fun k => s (Sum.inr k))) :=
    hfront.sum_refinement hW F g η
      (fun j => (hF j).continuousOn) (fun k => ((hg k).mono subset_closure).continuousOn) hzero
  let T := analyticSignAffineCoordinates e x₀
  let V : Set (Fin (d + 1) → ℝ) := T.symm ⁻¹' W
  let G : J ⊕ κ → (Fin (d + 1) → ℝ) → ℝ :=
    Sum.elim f (fun k y => g k (T.symm y))
  have hT0 : T 0 = x₀ := by simp [T]
  have hinv0 : T.symm x₀ = 0 := by
    calc
      T.symm x₀ = T.symm (T 0) := congrArg T.symm hT0.symm
      _ = 0 := T.symm_apply_apply 0
  have hfamily : G = fun q y => Sum.elim F g q (T.symm y) := by
    funext q y
    rcases q with j | k
    · change f j y = f j (x₀ + e (T.symm y))
      congr 1
      exact (T.apply_symm_apply y).symm
    · rfl
  refine ⟨V, hW.preimage T.symm.continuous, ?_, ?_, ?_, J ⊕ κ, inferInstance, G, (fun s => η (fun k => s (Sum.inr k))), ?_, ?_, ?_, ?_⟩
  · change T.symm x₀ ∈ W
    rw [hinv0]
    exact h0W
  · intro y hy
    have hyW : T.symm y ∈ closure W := by
      change y ∈ T.symm ⁻¹' closure W
      rw [T.symm.preimage_closure]
      exact hy
    have hd := hdomain (T.symm y) (hclosedWD hyW)
    change T (T.symm y) ∈ O at hd
    simpa only [T.apply_symm_apply] using hd
  · have hsemi := hBsemi.affineCylinderImage e x₀ (-(r / 2)) (r / 2)
    have heV : V = (fun z => x₀ + e z) '' W := by
      exact (T.image_eq_preimage_symm W).symm
    rw [heV]
    exact hsemi
  · rw [hfamily]
    intro q y hy
    have hyW : T.symm y ∈ closure W := by
      change y ∈ T.symm ⁻¹' closure W
      rw [T.symm.preimage_closure]
      exact hy
    exact (hsumA q (T.symm y) hyW).comp
      (analyticAt_analyticSignAffineCoordinates_symm e x₀ y)
  · exact fun j => ⟨Sum.inl j, fun _ _ => rfl⟩
  · rw [hfamily]
    have hTa (z : (Fin d → ℝ) × ℝ) : AnalyticAt ℝ T z := by
      change AnalyticAt ℝ (fun w => x₀ + e w) z
      exact analyticAt_const.add (e.analyticAt z)
    exact hsep.homeomorph T hTa (analyticAt_analyticSignAffineCoordinates_symm e x₀)


  · intro s hne
    rw [hfamily] at hne ⊢
    have hreg := hregular.sum_refinement F g η
    have hsource : (analyticStrongSignCell W (Sum.elim F g) s).Nonempty := by
      obtain ⟨y, hy⟩ := hne
      exact ⟨T.symm y, hy⟩
    have hTa (z : (Fin d → ℝ) × ℝ) : AnalyticAt ℝ T z := by
      change AnalyticAt ℝ (fun w => x₀ + e w) z
      exact analyticAt_const.add (e.analyticAt z)
    have hTi := analyticAt_analyticSignAffineCoordinates_symm e x₀
    have hn := (hreg s hsource).transport
      (fun _ hx => subset_closure hx.1) T e.toLinearEquiv.finrank_eq hTi
      (analytic_homeomorph_symm_fderiv_surjective T hTa hTi)
    rw [T.symm.preimage_closure, T.image_eq_preimage_symm,
      ← analyticStrongSignCell_preimage] at hn
    exact hn

/-- A genuine analytic stratum refinement in every finite dimension,
including coherent chart dimensions and their strict decrease on every
proper nonempty weak-sign face. No lower-dimensional input remains. -/
theorem localAnalyticRegularRefinement_fin (d : ℕ) :
    LocalAnalyticRegularRefinement d := by
  induction d with
  | zero => exact localAnalyticRegularRefinement_of_subsingleton 0
  | succ d ih => exact localAnalyticRegularRefinement_succ d ih

end PlanarNikodym
