import PlanarNikodym.Geometry.AnalyticConnectedSeparationPreparation
import PlanarNikodym.Geometry.PolynomialConnectedRefinementLifting

/-! Dimension induction for finite analytic connected sign refinements.
The successor step constructs common Weierstrass coordinates, applies the
proved polynomial lifting theorem to the lower-dimensional conclusion,
restores the original functions by their actual zero sets, and transports
the finite refinement back to the original prescribed neighborhood. -/
noncomputable section
open Set Metric Polynomial
namespace PlanarNikodym

theorem localAnalyticConnectedRefinement_of_subsingleton
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [Subsingleton E] :
    LocalAnalyticConnectedRefinement E := by
  intro J _ f x₀ ha O _ hxO
  refine ⟨univ, isOpen_univ, mem_univ _, ?_, J, inferInstance, f, ?_, ?_, ?_⟩
  · intro y _
    have hy : y = x₀ := Subsingleton.elim _ _
    exact hy ▸ hxO
  · intro j y _
    have hy : y = x₀ := Subsingleton.elim _ _
    exact hy ▸ ha j
  · exact fun j => ⟨j, fun _ _ => rfl⟩
  · intro s
    rcases (analyticStrongSignCell univ f s).eq_empty_or_nonempty with he | hne
    · exact Or.inl he
    · right
      refine ⟨hne, ?_⟩
      have hs : (analyticStrongSignCell univ f s).Subsingleton :=
        fun x _ y _ => Subsingleton.elim x y
      exact hs.isPreconnected

theorem localAnalyticConnectedRefinement_succ (d : ℕ)
    (H : LocalAnalyticConnectedRefinement (Fin d → ℝ)) :
    LocalAnalyticConnectedRefinement (Fin (d + 1) → ℝ) := by
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
  obtain ⟨B, hB, h0B, hBε, κ, hκ, g, hg, hinc, hconn⟩ :=
    exists_polynomial_connected_refinement_lifting H m a ε r hε hr ha'
  let W : Set ((Fin d → ℝ) × ℝ) := B ×ˢ Ioo (-r) r
  have hWD : W ⊆ D := fun _ hz => ⟨hBε hz.1, hz.2⟩
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
  have hsumA (q : J ⊕ κ) : AnalyticOnNhd ℝ (Sum.elim F g q) W := by
    rcases q with j | k
    · exact hF j
    · exact hg k
  have hsep (s : J ⊕ κ → Fin 3) :
      analyticStrongSignCell W (Sum.elim F g) s = ∅ ∨
        IsConnected (analyticStrongSignCell W (Sum.elim F g) s) :=
    analyticStrongSignCell_sum_connected_or_empty W F g
      (fun j => (hF j).continuousOn) hzero hconn s
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
  refine ⟨V, hW.preimage T.symm.continuous, ?_, ?_, J ⊕ κ, inferInstance, G, ?_, ?_, ?_⟩
  · change T.symm x₀ ∈ W
    rw [hinv0]
    exact h0W
  · intro y hy
    have hd := hdomain (T.symm y) (hWD hy)
    change T (T.symm y) ∈ O at hd
    simpa only [T.apply_symm_apply] using hd
  · rw [hfamily]
    intro q y hy
    exact (hsumA q (T.symm y) hy).comp
      (analyticAt_analyticSignAffineCoordinates_symm e x₀ y)
  · exact fun j => ⟨Sum.inl j, fun _ _ => rfl⟩
  · rw [hfamily]
    exact analyticStrongSignCell_connected_or_empty_homeomorph T.symm W _ hsep

/-- Every finite family of real analytic germs in every finite dimension
has an actual finite analytic connected sign refinement inside any given
open neighborhood. No cell-decomposition or refinement input remains. -/
theorem localAnalyticConnectedRefinement_fin (d : ℕ) :
    LocalAnalyticConnectedRefinement (Fin d → ℝ) := by
  induction d with
  | zero => exact localAnalyticConnectedRefinement_of_subsingleton _
  | succ d ih => exact localAnalyticConnectedRefinement_succ d ih

end PlanarNikodym
