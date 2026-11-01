import PlanarNikodym.Tame.PiecewiseAnalyticGerms
import PlanarNikodym.Tame.RestrictedAnalyticLanguage

/-! Every actual term of the restricted analytic real language has a finite
semianalytic local analytic presentation. No quantifier elimination is used. -/
noncomputable section
open Set Filter FirstOrder FirstOrder.Language
open scoped Topology
namespace PlanarNikodym

theorem restrictedAnalyticFunction_piecewiseAnalyticAt {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf : AnalyticOnNhd ℝ f (restrictedAnalyticCube n))
    (a : Fin n → ℝ) : PiecewiseAnalyticAt (restrictedAnalyticFunction f) a := by
  classical
  by_cases ha : a ∈ restrictedAnalyticCube n
  · refine ⟨Bool, inferInstance,
      (fun b => if b then restrictedAnalyticCube n else (restrictedAnalyticCube n)ᶜ),
      (fun b => if b then f else fun _ => 0), ?_, ?_, ?_⟩
    · intro b
      cases b
      · exact LocallySemianalytic.compl (locallySemianalytic_restrictedAnalyticCube n) a
      · exact locallySemianalytic_restrictedAnalyticCube n a
    · intro b
      cases b
      · exact analyticAt_const
      · exact hf a ha
    · apply Eventually.of_forall
      intro x
      constructor
      · by_cases hx : x ∈ restrictedAnalyticCube n
        · exact ⟨true, hx⟩
        · exact ⟨false, hx⟩
      · intro b hb
        cases b
        · exact if_neg hb
        · exact if_pos hb
  · have he : (fun _ : Fin n → ℝ => (0 : ℝ)) =ᶠ[𝓝 a] restrictedAnalyticFunction f := by
      filter_upwards [(isClosed_Icc.isOpen_compl.mem_nhds ha)] with x hx
      exact (if_neg hx).symm
    exact (AnalyticAt.piecewiseAnalyticAt analyticAt_const).congr he

theorem restrictedAnalyticSymbol_piecewiseAnalyticAt {n : ℕ}
    (s : RestrictedAnalyticSymbol n) (a : Fin n → ℝ) :
    PiecewiseAnalyticAt (Structure.funMap (L := restrictedAnalyticLanguage) (M := ℝ) s) a := by
  cases s with
  | constant c => exact AnalyticAt.piecewiseAnalyticAt analyticAt_const
  | add => exact AnalyticAt.piecewiseAnalyticAt ((analyticAt_coordinate 0 a).add (analyticAt_coordinate 1 a))
  | mul => exact AnalyticAt.piecewiseAnalyticAt ((analyticAt_coordinate 0 a).mul (analyticAt_coordinate 1 a))
  | neg => exact AnalyticAt.piecewiseAnalyticAt (analyticAt_coordinate 0 a).neg
  | analytic f hf => exact restrictedAnalyticFunction_piecewiseAnalyticAt f hf a

theorem restrictedAnalyticTerm_realize_piecewiseAnalyticAt {n : ℕ} {α : Type*}
    (t : restrictedAnalyticLanguage.Term α) (v : (Fin n → ℝ) → α → ℝ)
    (a : Fin n → ℝ) (hv : ∀ i, PiecewiseAnalyticAt (fun x => v x i) a) :
    PiecewiseAnalyticAt (fun x => t.realize (v x)) a := by
  induction t with
  | var i => exact hv i
  | @func m s ts ih =>
    exact PiecewiseAnalyticAt.comp (restrictedAnalyticSymbol_piecewiseAnalyticAt s)
      (PiecewiseAnalyticAt.pi (fun i => ih i))

theorem restrictedAnalyticTerm_piecewiseAnalyticAt {n : ℕ}
    (t : restrictedAnalyticLanguage.Term (Fin n)) (a : Fin n → ℝ) :
    PiecewiseAnalyticAt (fun x => t.realize x) a :=
  restrictedAnalyticTerm_realize_piecewiseAnalyticAt t (fun x => x) a
    (fun i => AnalyticAt.piecewiseAnalyticAt (analyticAt_coordinate i a))

end PlanarNikodym
