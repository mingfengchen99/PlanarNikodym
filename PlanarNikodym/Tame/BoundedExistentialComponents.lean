import PlanarNikodym.Tame.QuantifierFreeSemianalytic

/-! Actual bounded existential projections of the original R_an language.
The boundedness assumption controls the full witness set, not merely its
projection. Arbitrary alternating quantifiers are not treated here. -/
noncomputable section
open Set FirstOrder FirstOrder.Language
namespace PlanarNikodym

theorem restrictedAnalyticQF_bounded_exists_components {n m : ℕ}
    (φ : restrictedAnalyticLanguage.Formula (Fin (n + m))) (hφ : φ.IsQF)
    (hb : Bornology.IsBounded {w : Fin (n + m) → ℝ | φ.Realize w}) :
    (componentDomains {x : Fin n → ℝ | ∃ y : Fin m → ℝ, φ.Realize (Fin.append x y)}).Finite ∧
      ∀ x : Fin n → ℝ, RanDefinable (_root_.connectedComponentIn
        {x : Fin n → ℝ | ∃ y : Fin m → ℝ, φ.Realize (Fin.append x y)} x) := by
  let F : (Fin (n + m) → ℝ) → (Fin n → ℝ) := fun w i => w (Fin.castAdd m i)
  have hF : ∀ w, AnalyticAt ℝ F w :=
    fun w => analyticAt_pi_iff.mpr (fun i => analyticAt_coordinate (Fin.castAdd m i) w)
  have he : F '' {w : Fin (n + m) → ℝ | φ.Realize w} =
      {x : Fin n → ℝ | ∃ y : Fin m → ℝ, φ.Realize (Fin.append x y)} := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨(fun i => w (Fin.natAdd n i)), ?_⟩
      have hsplit : Fin.append (F w) (fun i => w (Fin.natAdd n i)) = w := by
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · exact Fin.append_left _ _ j
        · exact Fin.append_right _ _ j
      rwa [hsplit]
    · rintro ⟨y, hy⟩
      exact ⟨Fin.append x y, hy, funext (fun i => Fin.append_left x y i)⟩
  rw [← he]
  exact restrictedAnalyticQF_finite_definable_image_components φ hφ hb F (fun w _ => hF w)

end PlanarNikodym
