import PlanarNikodym.Geometry.AnalyticIntervalPartition
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The order-connected part of Thom's lemma, with both strict and weak
sign conditions. Derivative signs are imposed on the actual polynomials.
No decomposition or connectedness premise is used. -/
noncomputable section
open Set Polynomial
namespace PlanarNikodym

def polynomialSignCondition (weak : Bool) (s : Fin 3) (r : ℝ) : Prop :=
  if weak then if s = 0 then r ≤ 0 else if s = 1 then r = 0 else 0 ≤ r
  else oneDimensionalSign r = s

theorem polynomialSignCondition_ordConnected (weak : Bool) (s : Fin 3) :
    {r : ℝ | polynomialSignCondition weak s r}.OrdConnected := by
  refine ⟨?_⟩
  intro x hx y hy t ht
  cases weak <;> fin_cases s <;>
    simp_all [polynomialSignCondition, oneDimensionalSign_eq_zero,
      oneDimensionalSign_eq_one, oneDimensionalSign_eq_two]
  all_goals linarith

theorem polynomialSignCondition_nonpos {weak : Bool} {r : ℝ}
    (h : polynomialSignCondition weak 0 r) : r ≤ 0 := by
  cases weak <;>
    simp_all [polynomialSignCondition, oneDimensionalSign_eq_zero]
  all_goals linarith

theorem polynomialSignCondition_nonneg {weak : Bool} {s : Fin 3} {r : ℝ}
    (hs : s ≠ 0) (h : polynomialSignCondition weak s r) : 0 ≤ r := by
  cases weak <;> fin_cases s <;>
    simp_all [polynomialSignCondition, oneDimensionalSign_eq_one,
      oneDimensionalSign_eq_two]
  all_goals linarith

theorem polynomialSignCondition_weaken {s : Fin 3} {r : ℝ}
    (h : polynomialSignCondition false s r) : polynomialSignCondition true s r := by
  fin_cases s <;>
    simp_all [polynomialSignCondition, oneDimensionalSign_eq_zero,
      oneDimensionalSign_eq_one, oneDimensionalSign_eq_two]
  all_goals linarith

theorem polynomialSignCondition_ne_zero {s : Fin 3} {r : ℝ}
    (hs : s ≠ 1) (h : polynomialSignCondition false s r) : r ≠ 0 := by
  intro hz
  apply hs
  change oneDimensionalSign r = s at h
  rw [hz] at h
  simpa [oneDimensionalSign] using h.symm

theorem polynomialSignCondition_strict_of_weak {s : Fin 3} {r : ℝ}
    (h : polynomialSignCondition true s r) (hn : s ≠ 1 → r ≠ 0) :
    polynomialSignCondition false s r := by
  fin_cases s
  · have hr : r ≤ 0 := by simpa [polynomialSignCondition] using h
    exact oneDimensionalSign_eq_zero.mpr (lt_of_le_of_ne hr (hn (by decide)))
  · have hr : r = 0 := by simpa [polynomialSignCondition] using h
    exact oneDimensionalSign_eq_one.mpr hr
  · have hr : 0 ≤ r := by simpa [polynomialSignCondition] using h
    exact oneDimensionalSign_eq_two.mpr (lt_of_le_of_ne hr (Ne.symm (hn (by decide))))

theorem isClosed_polynomialWeakSignCondition (s : Fin 3) :
    IsClosed {r : ℝ | polynomialSignCondition true s r} := by
  fin_cases s
  · change IsClosed (Iic (0 : ℝ))
    exact isClosed_Iic
  · change IsClosed ({0} : Set ℝ)
    exact isClosed_singleton
  · change IsClosed (Ici (0 : ℝ))
    exact isClosed_Ici

def polynomialThomJetCell (weak : Bool) (P : ℝ[X]) (N : ℕ)
    (s : ℕ → Fin 3) : Set ℝ :=
  {x | ∀ k ≤ N, polynomialSignCondition weak (s k) ((derivative^[k] P).eval x)}

theorem polynomialThomJetCell_succ (weak : Bool) (P : ℝ[X]) (N : ℕ)
    (s : ℕ → Fin 3) :
    polynomialThomJetCell weak P (N + 1) s =
      polynomialThomJetCell weak P.derivative N (fun k => s (k + 1)) ∩
        {x | polynomialSignCondition weak (s 0) (P.eval x)} := by
  ext x
  constructor
  · intro hx
    refine ⟨fun k hk => ?_, ?_⟩
    · simpa only [Function.iterate_succ_apply] using hx (k + 1) (by omega)
    · simpa only [Function.iterate_zero_apply, Set.mem_setOf_eq] using hx 0 (by omega)
  · rintro ⟨ht, h0⟩ k hk
    cases k with
    | zero => simpa only [Function.iterate_zero_apply, Set.mem_setOf_eq] using h0
    | succ k =>
      simpa only [Function.iterate_succ_apply] using ht k (by omega)

/-- Every strict or weak full derivative sign cell of an actual polynomial
is order connected, including zero and constant polynomials. -/
theorem polynomialThomJetCell_ordConnected (weak : Bool) (P : ℝ[X])
    (N : ℕ) (hP : P.natDegree ≤ N) (s : ℕ → Fin 3) :
    (polynomialThomJetCell weak P N s).OrdConnected := by
  induction N generalizing P s with
  | zero =>
    have hp : P.natDegree = 0 := Nat.eq_zero_of_le_zero hP
    have he := eq_C_of_natDegree_eq_zero hp
    refine ⟨?_⟩
    intro x hx y _ t _ k hk
    have hk0 : k = 0 := by omega
    subst k
    have hv : P.eval t = P.eval x := by
      conv_lhs => rw [he, eval_C]
      conv_rhs => rw [he, eval_C]
    simpa only [Function.iterate_zero_apply, hv] using hx 0 (by omega)
  | succ N ih =>
    let T := polynomialThomJetCell weak P.derivative N (fun k => s (k + 1))
    have hd : P.derivative.natDegree ≤ N :=
      (natDegree_derivative_le P).trans (by omega)
    have hT : T.OrdConnected := ih P.derivative hd _
    have hsign (x : ℝ) (hx : x ∈ T) :
        polynomialSignCondition weak (s 1) (P.derivative.eval x) := by
      simpa only [Function.iterate_zero_apply] using hx 0 (Nat.zero_le N)
    have htarget := polynomialSignCondition_ordConnected weak (s 0)
    rw [polynomialThomJetCell_succ]
    change (T ∩ (fun x => P.eval x) ⁻¹' {r : ℝ | polynomialSignCondition weak (s 0) r}).OrdConnected
    by_cases hneg : s 1 = 0
    · have ha : AntitoneOn (fun x => P.eval x) T :=
        antitoneOn_of_deriv_nonpos hT.convex P.continuous.continuousOn
          P.differentiableOn (fun x hx => by
            rw [P.deriv]
            exact polynomialSignCondition_nonpos (hneg ▸ hsign x (interior_subset hx)))
      obtain ⟨V, hV, he⟩ := htarget.preimage_antitoneOn ha
      rw [he]
      exact hT.inter hV
    · have hm : MonotoneOn (fun x => P.eval x) T :=
        monotoneOn_of_deriv_nonneg hT.convex P.continuous.continuousOn
          P.differentiableOn (fun x hx => by
            rw [P.deriv]
            exact polynomialSignCondition_nonneg hneg (hsign x (interior_subset hx)))
      obtain ⟨V, hV, he⟩ := htarget.preimage_monotoneOn hm
      rw [he]
      exact hT.inter hV

end PlanarNikodym
