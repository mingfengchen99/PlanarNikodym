import PlanarNikodym.Geometry.WeierstrassBanachDivision
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.Banach

/-! Local injectivity of the actual bounded-series division operator. -/

noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym

theorem continuous_weierstrassDivisionOperator (m : ℕ) :
    Continuous (weierstrassDivisionOperator m) := by
  unfold weierstrassDivisionOperator
  fun_prop

/-- The polynomial division operator stays injective for all sufficiently small lower
coefficients. This is operator-norm openness of the invertible Banach endomorphisms,
after identifying the target with its finite head and infinite tail. -/
theorem eventually_weierstrassDivisionOperator_injective (m : ℕ) :
    ∀ᶠ a : Fin m → ℝ in 𝓝 0,
      Function.Injective (weierstrassDivisionOperator m a) := by
  let A : (Fin m → ℝ) → WeierstrassFactors m →L[ℝ] WeierstrassFactors m :=
    fun a => (weierstrassSplit m).toContinuousLinearMap.comp
      (weierstrassDivisionOperator m a)
  have hA : Continuous A :=
    (continuous_weierstrassDivisionOperator m).const_clm_comp _
  have hA₀ : A 0 = 1 := by
    apply ContinuousLinearMap.ext
    intro w
    change weierstrassSplit m (weierstrassDivisionOperator m 0 w) = w
    rw [weierstrassDivisionOperator_zero, ← weierstrassSplit_symm_apply]
    exact (weierstrassSplit m).apply_symm_apply w
  have hi : ∀ᶠ a in 𝓝 (0 : Fin m → ℝ), IsUnit (A a) :=
    hA.continuousAt.eventually (Units.isOpen.mem_nhds (by rw [hA₀]; exact isUnit_one))
  filter_upwards [hi] with a ha
  have hj := (ContinuousLinearMap.isUnit_iff_bijective.mp ha).injective
  intro u v huv
  exact hj (congrArg (weierstrassSplit m) huv)

end PlanarNikodym
