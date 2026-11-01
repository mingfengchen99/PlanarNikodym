import PlanarNikodym.Analysis.Fourier.GlyzProjectedCurve
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Ring.Units

/-! Actual orthogonal projection through an injective frame. The Gram
inverse formula proves continuity without making a continuous choice of
orthonormal bases. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Submodule
namespace PlanarNikodym

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem glyz_isUnit_gram (R : E →L[ℝ] F) (hR : Function.Injective R) :
    IsUnit (R.adjoint.comp R) := by
  have hi : Function.Injective (R.adjoint.comp R) :=
    LinearMap.ker_eq_bot.mp (by rw [R.ker_adjoint_comp_self]; exact LinearMap.ker_eq_bot.mpr hR)
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

theorem glyz_range_starProjection (R : E →L[ℝ] F) (hR : Function.Injective R) :
    R.range.starProjection = R.comp ((Ring.inverse (R.adjoint.comp R)).comp R.adjoint) := by
  let A := R.adjoint.comp R
  have hA : IsUnit A := glyz_isUnit_gram R hR
  have hi (v : E) : A (Ring.inverse A v) = v :=
    congrArg (fun B : E →L[ℝ] E => B v) (Ring.mul_inverse_cancel A hA)
  ext x
  apply R.range.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨Ring.inverse A (R.adjoint x), rfl⟩
  · rintro _ ⟨v, rfl⟩
    change inner ℝ (x - R (Ring.inverse A (R.adjoint x))) (R v) = 0
    rw [← R.adjoint_inner_left, map_sub]
    change inner ℝ (R.adjoint x - A (Ring.inverse A (R.adjoint x))) v = 0
    rw [hi, sub_self, inner_zero_left]

theorem glyz_continuous_range_starProjection {X : Type*} [TopologicalSpace X]
    (R : X → E →L[ℝ] F) (hc : Continuous R) (hi : ∀ x, Function.Injective (R x)) :
    Continuous (fun x => (R x).range.starProjection) := by
  have ha : Continuous (fun x => (R x).adjoint) :=
    ContinuousLinearMap.adjoint.continuous.comp hc
  have hg : Continuous (fun x => (R x).adjoint.comp (R x)) := ha.clm_comp hc
  have hinv : Continuous (fun x => Ring.inverse ((R x).adjoint.comp (R x))) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    obtain ⟨u, hu⟩ := glyz_isUnit_gram (R x) (hi x)
    have huinv : ContinuousAt Ring.inverse ((R x).adjoint.comp (R x)) :=
      hu ▸ NormedRing.inverse_continuousAt u
    exact ContinuousAt.comp (f := fun y => (R y).adjoint.comp (R y)) (g := Ring.inverse) (x := x) huinv hg.continuousAt
  have he : (fun x => (R x).range.starProjection) =
      fun x => (R x).comp ((Ring.inverse ((R x).adjoint.comp (R x))).comp (R x).adjoint) :=
    funext fun x => glyz_range_starProjection (R x) (hi x)
  rw [he]
  exact hc.clm_comp (hinv.clm_comp ha)

end PlanarNikodym
