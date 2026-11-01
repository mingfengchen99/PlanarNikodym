import PlanarNikodym.Geometry.AnalyticDivisionSeries
import Mathlib.Analysis.Analytic.Constructions

/-! Division by any power of the last coordinate in the actual analytic
germ. The remainder has finitely many parameter-analytic coefficients,
and the quotient is jointly analytic. This monomial division does not
assert division by a general Weierstrass-regular analytic function. -/

noncomputable section
open Set Filter
open scoped Topology

namespace PlanarNikodym
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Actual analytic division by `(t-t₀)^m`, including order zero.
All coefficient germs and the quotient are constructed from the given
analytic germ; no convergence or remainder estimate is a premise. -/
theorem exists_analytic_monomial_division (f : E × ℝ → F) (x₀ : E) (t₀ : ℝ)
    (hf : AnalyticAt ℝ f (x₀, t₀)) (m : ℕ) :
    ∃ (a : Fin m → E → F) (q : E × ℝ → F),
      (∀ i, AnalyticAt ℝ (a i) x₀) ∧ AnalyticAt ℝ q (x₀, t₀) ∧
        ∀ᶠ z in 𝓝 (x₀, t₀),
          f z = (∑ i : Fin m, (z.2 - t₀) ^ (i : ℕ) • a i z.1) +
            (z.2 - t₀) ^ m • q z := by
  induction m generalizing f with
  | zero =>
    refine ⟨fun i => Fin.elim0 i, f, fun i => Fin.elim0 i, hf, ?_⟩
    exact Filter.Eventually.of_forall (fun z => by simp)
  | succ m ih =>
    obtain ⟨g, hg, he⟩ := exists_analytic_coordinate_quotient f x₀ t₀ hf
    obtain ⟨b, q, hb, hq, hsplit⟩ := ih g hg
    let a : Fin (m + 1) → E → F := Fin.cons (fun x => f (x, t₀)) b
    refine ⟨a, q, ?_, hq, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => hb j) i
      exact hf.comp (f := fun x : E => (x, t₀))
        (analyticAt_id.prod analyticAt_const)
    · filter_upwards [he, hsplit] with z hz hzg
      have hz' : f z = f (z.1, t₀) + (z.2 - t₀) • g z :=
        (sub_eq_iff_eq_add.mp hz).trans (add_comm _ _)
      rw [hz', hzg, smul_add, Fin.sum_univ_succ]
      simp only [a, Fin.cons_zero, Fin.val_zero, pow_zero, one_smul,
        Fin.cons_succ, Fin.val_succ]
      rw [Finset.smul_sum]
      have hs : ∑ i : Fin m, (z.2 - t₀) • ((z.2 - t₀) ^ (i : ℕ) • b i z.1) =
          ∑ i : Fin m, (z.2 - t₀) ^ ((i : ℕ) + 1) • b i z.1 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [smul_smul, pow_succ']
      rw [hs, smul_smul, ← pow_succ']
      exact (add_assoc _ _ _).symm

end PlanarNikodym
