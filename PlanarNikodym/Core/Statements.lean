import PlanarNikodym.Rank.Rank

/-! Statements of the analytic classification theorems.
This module defines the constant-rank conclusions and the public statements.
Their proofs are exported by `ProvedAnalyticClassification` (Theorem 1.5)
and `GeneralAnalyticClassification` (Theorem 1.4). -/
namespace PlanarNikodym
open Set

def ConstantRanks {d : ℕ} (G : Family 2 d) (mp mc : ℕ) : Prop :=
  ∀ p ∈ G.W, G.pointRank p = mp ∧ G.curveRank p = mc

/-- The conclusions of Theorem 1.5, with all reuse/foliation clauses retained. -/
def ConstantRankConclusions {d : ℕ} (G : Family 2 d) (mp mc : ℕ) : Prop :=
  (mc = mp + 2 → ¬ G.AdmitsNikodym ∧ ∀ p ∈ G.W, ¬ G.Reused (G.curve p)) ∧
  (mc = mp + 1 → mp = 0 →
    ¬ G.AdmitsNikodym ∧ ¬ G.HasMassiveCurveReuse ∧
    (∀ p ∈ G.W, G.LocallyReused p) ∧ G.HasLocalCurveReuse ∧ G.ReusedStronglyCovered) ∧
  (mc = mp + 1 → 0 < mp →
    G.AdmitsNikodym ∧ G.HasLocalCurveReuse ∧ G.LocalReuseNotCovered) ∧
  (mc = mp → G.AdmitsNikodym ∧ G.HasMassiveCurveReuse)

def Theorem15Statement : Prop :=
  ∀ (d : ℕ) (G : Family 2 d) (mp mc : ℕ),
    G.W.Nonempty → IsOpen G.W → Bornology.IsBounded G.W → G.IsAnalytic →
    ConstantRanks G mp mc → ConstantRankConclusions G mp mc

/-- Theorem 1.4, as a target proposition rather than an axiom. -/
def Theorem14Statement : Prop :=
  ∀ (d : ℕ) (G : Family 2 d), IsOpen G.W → G.IsAnalyticAtClosure →
    (G.AdmitsNikodym ↔ G.HasMassiveCurveReuse ∨ G.LocalReuseNotCovered)

end PlanarNikodym
