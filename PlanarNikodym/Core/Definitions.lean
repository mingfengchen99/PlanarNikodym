import Mathlib.Analysis.Analytic.Constructions
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Core objects for arXiv:2609.39217v1, Definitions 1.1–1.9.
The defining function is an ambient extension; all curve identities and ranks
are restricted to `I.carrier`. Regularity is a separate, explicit predicate. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace PlanarNikodym

abbrev Plane := ℝ × ℝ
abbrev Base (n : ℕ) := Fin n → ℝ
abbrev Aux (d : ℕ) := Fin d → ℝ
abbrev Parameters (n d : ℕ) := Base n × Aux d

structure Interval where
  left : ℝ
  right : ℝ
  nondegenerate : left < right

def Interval.carrier (I : Interval) : Set ℝ := Icc I.left I.right

structure Family (n d : ℕ) where
  I : Interval
  W : Set (Parameters n d)
  γ : ℝ → Parameters n d → ℝ

namespace Family
variable {n d : ℕ} (G : Family n d)

def IsSmooth : Prop :=
  ContDiffOn ℝ ∞ (fun x : ℝ × Parameters n d => G.γ x.1 x.2) (G.I.carrier ×ˢ G.W)

/-- Analytic in an ambient neighbourhood at every point, including endpoints. -/
def IsAnalytic : Prop :=
  AnalyticOnNhd ℝ (fun x : ℝ × Parameters n d => G.γ x.1 x.2)
    (G.I.carrier ×ˢ G.W)

def IsAnalyticAtClosure : Prop :=
  AnalyticOnNhd ℝ (fun x : ℝ × Parameters n d => G.γ x.1 x.2)
    (G.I.carrier ×ˢ closure G.W)

def graphMap (p : Parameters n d) (t : ℝ) : Plane := (t, G.γ t p)
def curve (p : Parameters n d) : Set Plane := G.graphMap p '' G.I.carrier
def SameCurve (p q : Parameters n d) : Prop :=
  ∀ t ∈ G.I.carrier, G.γ t p = G.γ t q

theorem sameCurve_iff_curve_eq (p q : Parameters n d) :
    G.SameCurve p q ↔ G.curve p = G.curve q := by
  constructor
  · intro h
    apply Set.image_congr
    intro t ht
    exact Prod.ext rfl (h t ht)
  · intro h t ht
    have : G.graphMap p t ∈ G.curve q := h ▸ Set.mem_image_of_mem _ ht
    rcases this with ⟨s, hs, he⟩
    have hst : s = t := congrArg Prod.fst he
    subst s
    exact (congrArg Prod.snd he).symm

def parametersOf (β : Set Plane) : Set (Parameters n d) :=
  {p | p ∈ G.W ∧ G.curve p = β}
def centersOf (β : Set Plane) : Set (Base n) := Prod.fst '' G.parametersOf β

/-- The original Borel/Hausdorff formulation (Definition 1.2). -/
def AdmitsNikodym : Prop :=
  ∃ E : Set Plane, ∃ F : Set (Base n),
    MeasurableSet E ∧ MeasurableSet F ∧ volume E = 0 ∧ 0 < volume F ∧
    ∀ z ∈ F, ∃ u : Aux d, (z, u) ∈ G.W ∧
      0 < Measure.hausdorffMeasure 1 (G.curve (z, u) ∩ E)

end Family

/-- Positive inner measure, so no measurability of a projection is assumed. -/
def HasPositivePart {X : Type*} [MeasurableSpace X] (μ : Measure X) (S : Set X) : Prop :=
  ∃ A : Set X, A ⊆ S ∧ MeasurableSet A ∧ 0 < μ A

namespace Family
variable {d : ℕ} (G : Family 2 d)

def Reused (β : Set Plane) : Prop :=
  HasPositivePart (Measure.hausdorffMeasure 1) (G.centersOf β)
def MassivelyReused (β : Set Plane) : Prop := HasPositivePart volume (G.centersOf β)
def LocallyReused (p : Parameters 2 d) : Prop :=
  p ∈ G.W ∧ ∀ U ∈ 𝓝 p,
    HasPositivePart (Measure.hausdorffMeasure 1)
      (Prod.fst '' (G.parametersOf (G.curve p) ∩ U))
def HasCurveReuse : Prop :=
  HasPositivePart volume {z | ∃ β, G.Reused β ∧ z ∈ G.centersOf β}
def HasMassiveCurveReuse : Prop := ∃ β, G.MassivelyReused β
def HasLocalCurveReuse : Prop :=
  HasPositivePart volume {z | ∃ u, G.LocallyReused (z, u)}

/-- A countable family is indexed by ℕ; finite families can be repeated. -/
structure Foliations where
  field : ℕ → Plane → Plane
  smooth : ∀ i, ContDiff ℝ ∞ (field i)

def wedge (v w : Plane) : ℝ := v.1 * w.2 - v.2 * w.1

/-- Coverage uses Hausdorff-a.e. points on the graph, independent of speed. -/
def Covered (V : Foliations) (p : Parameters 2 d) : Prop :=
  ∀ᵐ q ∂(Measure.hausdorffMeasure 1).restrict (G.curve p),
    ∃ i, V.field i q ≠ 0 ∧
      wedge (V.field i q) (1, deriv (fun t => G.γ t p) q.1) = 0

def CompletelyCovered (C : Set (Parameters 2 d)) : Prop :=
  ∃ V : Foliations, ∀ p ∈ C, G.Covered V p
def ReusedStronglyCovered : Prop :=
  ∃ V : Foliations, ∀ p ∈ G.W, G.Reused (G.curve p) → G.Covered V p
def ReusedCovered : Prop :=
  ∃ V : Foliations,
    volume {z | ∃ u, (z, u) ∈ G.W ∧ G.Reused (G.curve (z, u)) ∧
      ¬ G.Covered V (z, u)} = 0
def uncoveredLocalCenters (V : Foliations) : Set (Base 2) :=
  {z | ∃ u, G.LocallyReused (z, u) ∧ ¬ G.Covered V (z, u)}
def LocallyReusedCovered : Prop :=
  ∃ V : Foliations, volume (G.uncoveredLocalCenters V) = 0
def LocalReuseNotCovered : Prop :=
  ∀ V : Foliations, HasPositivePart volume (G.uncoveredLocalCenters V)

/-- Coordinate derivatives, viewed as functions on the interval subtype. -/
def uColumn (p : Parameters 2 d) (i : Fin d) : G.I.carrier → ℝ :=
  fun t => fderiv ℝ (fun u => G.γ t (p.1, u)) p.2 (Pi.single i 1)
def zColumn (p : Parameters 2 d) (i : Fin 2) : G.I.carrier → ℝ :=
  fun t => fderiv ℝ (fun z => G.γ t (z, p.2)) p.1 (Pi.single i 1)
def pointSpace (p : Parameters 2 d) : Submodule ℝ (G.I.carrier → ℝ) :=
  Submodule.span ℝ (Set.range (G.uColumn p))
def curveSpace (p : Parameters 2 d) : Submodule ℝ (G.I.carrier → ℝ) :=
  G.pointSpace p ⊔ Submodule.span ℝ (Set.range (G.zColumn p))
def pointRank (p : Parameters 2 d) : ℕ := Module.finrank ℝ (G.pointSpace p)
def curveRank (p : Parameters 2 d) : ℕ := Module.finrank ℝ (G.curveSpace p)

end Family
end PlanarNikodym
