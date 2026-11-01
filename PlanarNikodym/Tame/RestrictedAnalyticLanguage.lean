import PlanarNikodym.Core.Definitions
import Mathlib.ModelTheory.Definability
import Mathlib.Analysis.Analytic.ChangeOrigin

/-! The actual restricted analytic real structure. Its only nonalgebraic
symbols are functions analytic on a neighbourhood of the standard closed
cube, interpreted as zero outside that cube. Definability below means
first-order definability in this specific structure. No cell decomposition
or finiteness assertion is built into this definition. -/

noncomputable section
open Set FirstOrder FirstOrder.Language

namespace PlanarNikodym

def restrictedAnalyticCube (n : ℕ) : Set (Fin n → ℝ) := Icc (-1) 1

def restrictedAnalyticFunction {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : ℝ := by
  classical
  exact if x ∈ restrictedAnalyticCube n then f x else 0

inductive RestrictedAnalyticSymbol : ℕ → Type
  | constant (c : ℝ) : RestrictedAnalyticSymbol 0
  | add : RestrictedAnalyticSymbol 2
  | mul : RestrictedAnalyticSymbol 2
  | neg : RestrictedAnalyticSymbol 1
  | analytic {n : ℕ} (f : (Fin n → ℝ) → ℝ)
      (regular : AnalyticOnNhd ℝ f (restrictedAnalyticCube n)) :
      RestrictedAnalyticSymbol n

inductive RestrictedAnalyticRelation : ℕ → Type
  | lt : RestrictedAnalyticRelation 2

def restrictedAnalyticLanguage : FirstOrder.Language where
  Functions := RestrictedAnalyticSymbol
  Relations := RestrictedAnalyticRelation

instance restrictedAnalyticRealStructure : restrictedAnalyticLanguage.Structure ℝ where
  funMap := fun {_} f x => match f with
    | .constant c => c
    | .add => x 0 + x 1
    | .mul => x 0 * x 1
    | .neg => -x 0
    | .analytic f _ => restrictedAnalyticFunction f x
  RelMap := fun {_} r x => match r with
    | .lt => x 0 < x 1

/-- Definability with real parameters. Real constants are already named in
the language, so no additional parameter set is needed. -/
abbrev RanDefinable {ι : Type*} (S : Set (ι → ℝ)) : Prop :=
  (∅ : Set ℝ).Definable restrictedAnalyticLanguage S

abbrev RanDefinableFun {ι : Type*} (f : (ι → ℝ) → ℝ) : Prop :=
  (∅ : Set ℝ).DefinableFun restrictedAnalyticLanguage f

abbrev RanDefinableMap {ι κ : Type*} (f : (ι → ℝ) → (κ → ℝ)) : Prop :=
  (∅ : Set ℝ).DefinableMap restrictedAnalyticLanguage f

theorem ranDefinableFun_const {ι : Type*} (c : ℝ) :
    RanDefinableFun (fun _ : ι → ℝ => c) := by
  exact (Term.func (L := restrictedAnalyticLanguage)
    (RestrictedAnalyticSymbol.constant c) Fin.elim0).definableFun_realize

theorem ranDefinableFun_coordinate {ι : Type*} (i : ι) :
    RanDefinableFun (fun x : ι → ℝ => x i) :=
  Set.DefinableFun.proj restrictedAnalyticLanguage

theorem ranDefinableFun_add {ι : Type*} {f g : (ι → ℝ) → ℝ}
    (hf : RanDefinableFun f) (hg : RanDefinableFun g) :
    RanDefinableFun (fun x => f x + g x) := by
  have h : RanDefinableFun (fun x : Fin 2 → ℝ => x 0 + x 1) :=
    Set.DefinableFun.fun_symbol (L := restrictedAnalyticLanguage) RestrictedAnalyticSymbol.add
  exact h.comp (g := fun x i => ![f x, g x] i)
    (by intro i; fin_cases i <;> assumption)

theorem ranDefinableFun_mul {ι : Type*} {f g : (ι → ℝ) → ℝ}
    (hf : RanDefinableFun f) (hg : RanDefinableFun g) :
    RanDefinableFun (fun x => f x * g x) := by
  have h : RanDefinableFun (fun x : Fin 2 → ℝ => x 0 * x 1) :=
    Set.DefinableFun.fun_symbol (L := restrictedAnalyticLanguage) RestrictedAnalyticSymbol.mul
  exact h.comp (g := fun x i => ![f x, g x] i)
    (by intro i; fin_cases i <;> assumption)

theorem ranDefinableFun_neg {ι : Type*} {f : (ι → ℝ) → ℝ}
    (hf : RanDefinableFun f) : RanDefinableFun (fun x => -f x) := by
  have h : RanDefinableFun (fun x : Fin 1 → ℝ => -x 0) :=
    Set.DefinableFun.fun_symbol (L := restrictedAnalyticLanguage) RestrictedAnalyticSymbol.neg
  exact h.comp (g := fun x _ => f x) (by intro i; exact hf)

theorem ranDefinableFun_sub {ι : Type*} {f g : (ι → ℝ) → ℝ}
    (hf : RanDefinableFun f) (hg : RanDefinableFun g) :
    RanDefinableFun (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using ranDefinableFun_add hf (ranDefinableFun_neg hg)

theorem ranDefinableFun_restrictedAnalytic {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : AnalyticOnNhd ℝ f (restrictedAnalyticCube n)) :
    RanDefinableFun (restrictedAnalyticFunction f) :=
  Set.DefinableFun.fun_symbol (L := restrictedAnalyticLanguage)
    (RestrictedAnalyticSymbol.analytic f hf)

theorem ranDefinable_lt {ι : Type*} {f g : (ι → ℝ) → ℝ}
    (hf : RanDefinableFun f) (hg : RanDefinableFun g) :
    RanDefinable {x | f x < g x} := by
  have h : RanDefinable {x : Fin 2 → ℝ | x 0 < x 1} := by
    change (∅ : Set ℝ).Definable restrictedAnalyticLanguage _
    rw [Set.empty_definable_iff]
    exact ⟨FirstOrder.Language.Relations.formula
      (L := restrictedAnalyticLanguage) RestrictedAnalyticRelation.lt
      (fun i => Term.var i), rfl⟩
  simpa using h.preimage_map (F := fun x i => ![f x, g x] i)
    (by intro i; fin_cases i <;> assumption)

theorem ranDefinable_le {ι : Type*} {f g : (ι → ℝ) → ℝ}
    (hf : RanDefinableFun f) (hg : RanDefinableFun g) :
    RanDefinable {x | f x ≤ g x} := by
  simpa only [Set.compl_setOf, not_lt] using (ranDefinable_lt hg hf).compl

end PlanarNikodym
