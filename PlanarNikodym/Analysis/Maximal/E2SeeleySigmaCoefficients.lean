import PlanarNikodym.Analysis.Maximal.E2SeeleyCoefficients
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! The actual block coefficients viewed as one countable index family,
with absolute summability and all exact signed moments. -/
noncomputable section
open scoped BigOperators
namespace PlanarNikodym

abbrev E2SeeleyIndex := Σ n : ℕ, Fin (n + 1)
def e2SeeleyA (i : E2SeeleyIndex) : ℝ := e2SeeleyCoefficient i.1 i.2
def e2SeeleyB (i : E2SeeleyIndex) : ℝ := e2SeeleyReflectionNode i.1 i.2

theorem e2Seeley_summable_absolute_moment (j : ℕ) :
    Summable (fun i : E2SeeleyIndex => |e2SeeleyA i| * |e2SeeleyB i| ^ j) := by
  apply (summable_sigma_of_nonneg (fun i : E2SeeleyIndex =>
    mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) j))).mpr
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  simpa only [tsum_fintype, e2SeeleyA, e2SeeleyB] using
    e2SeeleyCoefficient_summable_absolute_moments j

theorem e2Seeley_summable_moment (j : ℕ) :
    Summable (fun i : E2SeeleyIndex => e2SeeleyA i * e2SeeleyB i ^ j) := by
  apply Summable.of_norm
  simpa only [Real.norm_eq_abs, abs_mul, abs_pow] using e2Seeley_summable_absolute_moment j

theorem e2Seeley_moment (j : ℕ) :
    ∑' i : E2SeeleyIndex, e2SeeleyA i * e2SeeleyB i ^ j = 1 := by
  rw [(e2Seeley_summable_moment j).tsum_sigma' (fun _ => (hasSum_fintype _).summable)]
  simpa only [tsum_fintype, e2SeeleyA, e2SeeleyB] using e2SeeleyCoefficient_all_moments j

theorem e2SeeleyB_neg (i : E2SeeleyIndex) : e2SeeleyB i < 0 := e2SeeleyReflectionNode_neg _ _

theorem e2SeeleyB_abs_ge_one (i : E2SeeleyIndex) : 1 ≤ |e2SeeleyB i| := by
  have hh := e2SeeleyReflectionNode_abs_ge_index i.1 i.2
  have hn : 0 ≤ (i.1 : ℝ) := Nat.cast_nonneg _
  unfold e2SeeleyB
  linarith

end PlanarNikodym
