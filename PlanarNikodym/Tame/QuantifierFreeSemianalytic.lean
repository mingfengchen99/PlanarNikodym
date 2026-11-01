import PlanarNikodym.Tame.RestrictedAnalyticTermGerms
import PlanarNikodym.Tame.DefinableContinuousImageComponents
import Mathlib.ModelTheory.Complexity

/-! Actual quantifier-free formulas, including nested restricted analytic
terms, define semianalytic sets. Bounded such sets and their continuous
coordinate images have finite definable topological components. -/
noncomputable section
open Set FirstOrder FirstOrder.Language
namespace PlanarNikodym

private theorem qf_zero_relation :
    LocallySemianalytic {x : Fin 2 → ℝ | x 0 = x 1} := by
  simpa only [sub_eq_zero] using locallySemianalytic_global_analytic_zero_set
    (fun x : Fin 2 → ℝ => x 0 - x 1)
    (fun x => (analyticAt_coordinate 0 x).sub (analyticAt_coordinate 1 x))

private theorem qf_lt_relation :
    LocallySemianalytic {x : Fin 2 → ℝ | x 0 < x 1} := by
  simpa only [sub_neg] using locallySemianalytic_global_analytic_sublevel
    (fun x : Fin 2 → ℝ => x 0 - x 1)
    (fun x => (analyticAt_coordinate 0 x).sub (analyticAt_coordinate 1 x))

theorem restrictedAnalyticQF_semianalyticAt {n l : ℕ} {α : Type*}
    {φ : restrictedAnalyticLanguage.BoundedFormula α l} (hφ : φ.IsQF)
    (v : (Fin n → ℝ) → α → ℝ) (xs : (Fin n → ℝ) → Fin l → ℝ)
    (a : Fin n → ℝ)
    (hv : ∀ i, PiecewiseAnalyticAt (fun x => v x i) a)
    (hxs : ∀ i, PiecewiseAnalyticAt (fun x => xs x i) a) :
    SemianalyticAt {x | φ.Realize (v x) (xs x)} a := by
  have hterm (t : restrictedAnalyticLanguage.Term (α ⊕ Fin l)) :
      PiecewiseAnalyticAt (fun x => t.realize (Sum.elim (v x) (xs x))) a := by
    apply restrictedAnalyticTerm_realize_piecewiseAnalyticAt
    rintro (i | i)
    · exact hv i
    · exact hxs i
  induction hφ with
  | falsum =>
    exact ⟨univ, isOpen_univ, mem_univ _, Fin 0, inferInstance,
      (fun i => Fin.elim0 i), (fun i => Fin.elim0 i), (fun _ => False), fun _ _ => Iff.rfl⟩
  | @of_isAtomic ψ hψ =>
    cases hψ with
    | equal t₁ t₂ =>
      let f (x : Fin n → ℝ) : Fin 2 → ℝ :=
        ![t₁.realize (Sum.elim (v x) (xs x)), t₂.realize (Sum.elim (v x) (xs x))]
      have hf : PiecewiseAnalyticAt f a := by
        apply PiecewiseAnalyticAt.pi
        intro i
        fin_cases i
        · exact hterm t₁
        · exact hterm t₂
      exact hf.preimage qf_zero_relation
    | @rel m r ts =>
      cases r with
      | lt =>
        have hf : PiecewiseAnalyticAt
            (fun x i => (ts i).realize (Sum.elim (v x) (xs x))) a :=
          PiecewiseAnalyticAt.pi (fun i => hterm (ts i))
        exact hf.preimage qf_lt_relation
  | @imp ψ χ hψ hχ ihψ ihχ =>
    convert (ihψ.inter ihχ.compl).compl using 1
    ext x
    simp only [mem_compl_iff, mem_inter_iff, mem_setOf_eq,
      BoundedFormula.realize_imp, not_and, not_not]

theorem restrictedAnalyticQF_locallySemianalytic {n : ℕ}
    (φ : restrictedAnalyticLanguage.Formula (Fin n)) (hφ : φ.IsQF) :
    LocallySemianalytic {x : Fin n → ℝ | φ.Realize x} := by
  intro a
  exact restrictedAnalyticQF_semianalyticAt hφ (fun x => x) (fun _ => Fin.elim0) a
    (fun i => AnalyticAt.piecewiseAnalyticAt (analyticAt_coordinate i a))
    (fun i => Fin.elim0 i)

theorem restrictedAnalyticQF_finite_definable_components {n : ℕ}
    (φ : restrictedAnalyticLanguage.Formula (Fin n)) (hφ : φ.IsQF)
    (hb : Bornology.IsBounded {x : Fin n → ℝ | φ.Realize x}) :
    (componentDomains {x : Fin n → ℝ | φ.Realize x}).Finite ∧
      ∀ x, RanDefinable (_root_.connectedComponentIn {x : Fin n → ℝ | φ.Realize x} x) := by
  have hA := restrictedAnalyticQF_locallySemianalytic φ hφ
  exact ⟨hA.components_finite_of_bounded hb,
    fun x => hA.ranDefinable_connectedComponentIn hb x⟩

theorem restrictedAnalyticQF_finite_definable_image_components {n : ℕ}
    {ι : Type*} [Fintype ι]
    (φ : restrictedAnalyticLanguage.Formula (Fin n)) (hφ : φ.IsQF)
    (hb : Bornology.IsBounded {x : Fin n → ℝ | φ.Realize x})
    (F : (Fin n → ℝ) → (ι → ℝ))
    (hF : AnalyticOnNhd ℝ F (closure {x : Fin n → ℝ | φ.Realize x})) :
    (componentDomains (F '' {x : Fin n → ℝ | φ.Realize x})).Finite ∧
      ∀ y, RanDefinable (_root_.connectedComponentIn (F '' {x : Fin n → ℝ | φ.Realize x}) y) :=
  (restrictedAnalyticQF_locallySemianalytic φ hφ).finite_definable_analytic_image_components hb F hF

end PlanarNikodym
