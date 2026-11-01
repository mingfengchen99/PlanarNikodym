import PlanarNikodym.Geometry.SemianalyticOperations
import PlanarNikodym.Tame.RestrictedAnalyticLanguage

/-! Concrete basic semianalytic sets and jointly analytic finite coordinate
maps, including the actual closed cube used by the R_an interpretation. -/
noncomputable section
open Set
namespace PlanarNikodym

theorem analyticAt_coordinate {n : ℕ} (i : Fin n) (x : Fin n → ℝ) :
    AnalyticAt ℝ (fun y : Fin n → ℝ => y i) x :=
  (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).analyticAt x

theorem analyticAt_finTail {n : ℕ} (x : Fin (n + 1) → ℝ) :
    AnalyticAt ℝ (Fin.tail : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) x :=
  analyticAt_pi_iff.mpr (fun i => analyticAt_coordinate i.succ x)

theorem locallySemianalytic_global_analytic_zero_set {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf : ∀ x, AnalyticAt ℝ f x) :
    LocallySemianalytic {x | f x = 0} := by
  apply locallySemianalytic_of_sign_description_at_closure
    (fun _ : Fin 1 => f) (fun _ x _ => hf x) (fun s => s 0 = 1)
  intro x
  exact oneDimensionalSign_eq_one.symm

theorem locallySemianalytic_global_analytic_sublevel {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf : ∀ x, AnalyticAt ℝ f x) :
    LocallySemianalytic {x | f x < 0} :=
  locallySemianalytic_analytic_sublevel (fun x _ => hf x)

theorem locallySemianalytic_restrictedAnalyticCube (n : ℕ) :
    LocallySemianalytic (restrictedAnalyticCube n) := by
  let A (i : Fin n) : Set (Fin n → ℝ) := {x | -1 ≤ x i ∧ x i ≤ 1}
  have hA (i : Fin n) : LocallySemianalytic (A i) := by
    have hlo := locallySemianalytic_global_analytic_sublevel (fun x : Fin n → ℝ => x i + 1)
      (fun x => (analyticAt_coordinate i x).add analyticAt_const)
    have hhi := locallySemianalytic_global_analytic_sublevel (fun x : Fin n → ℝ => 1 - x i)
      (fun x => analyticAt_const.sub (analyticAt_coordinate i x))
    convert hlo.compl.inter hhi.compl using 1
    ext x
    simp only [A, mem_inter_iff, mem_compl_iff, mem_setOf_eq, not_lt]
    constructor <;> rintro ⟨hl, hh⟩ <;> constructor <;> linarith
  have he : restrictedAnalyticCube n = ⋂ i, A i := by
    ext x
    simp only [restrictedAnalyticCube, A, mem_Icc, Pi.le_def, mem_iInter, mem_setOf_eq,
      Pi.neg_apply, Pi.one_apply]
    exact forall_and.symm
  rw [he]
  exact LocallySemianalytic.iInter A hA

theorem locallySemianalytic_global_analytic_graph {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf : ∀ x, AnalyticAt ℝ f x) :
    LocallySemianalytic {w : Fin (n + 1) → ℝ | f (Fin.tail w) = w 0} := by
  have h := locallySemianalytic_global_analytic_zero_set
    (fun w : Fin (n + 1) → ℝ => f (Fin.tail w) - w 0)
    (fun w => ((hf (Fin.tail w)).comp (analyticAt_finTail w)).sub (analyticAt_coordinate 0 w))
  simpa only [sub_eq_zero] using h

end PlanarNikodym
