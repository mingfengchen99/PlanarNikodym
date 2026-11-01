import PlanarNikodym.Analysis.Fourier.GlyzScaledCurveFrame

/-! The actual Taylor polynomial is an affine image of the standard
moment curve, with a constructed invertible linear map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped BigOperators
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem glyzTaylorCurve_eq_sum (γ : ℝ → E) (l : ℕ) (a s : ℝ) :
    glyzTaylorCurve γ l a s = γ a +
      ∑ j : Fin l, ((((j : ℕ) + 1).factorial : ℝ)⁻¹ * (s - a) ^ ((j : ℕ) + 1)) •
        iteratedDeriv ((j : ℕ) + 1) γ a := by
  rw [glyzTaylorCurve, taylor_within_apply]
  simp only [iteratedDerivWithin_univ]
  rw [Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, mul_one,
    iteratedDeriv_zero, one_smul]
  rw [add_comm]
  congr 1
  exact (Fin.sum_univ_eq_sum_range
    (fun j : ℕ => (((j + 1).factorial : ℝ)⁻¹ * (s - a) ^ (j + 1)) •
      iteratedDeriv (j + 1) γ a) l).symm

def glyzTaylorMomentLinear {l : ℕ} (L : GlyzSpace l ≃L[ℝ] GlyzSpace l) :
    GlyzSpace l ≃L[ℝ] GlyzSpace l :=
  (EuclideanSpace.equiv (Fin l) ℝ).trans
    ((coefficientDilation (fun j : Fin l => ((((j : ℕ) + 1).factorial : ℝ))⁻¹)
      (fun _ => by positivity)).trans ((EuclideanSpace.equiv (Fin l) ℝ).symm.trans L))

theorem glyzTaylorCurve_eq_affine_moment {l : ℕ} (γ : ℝ → GlyzSpace l) (a s : ℝ)
    (L : GlyzSpace l ≃L[ℝ] GlyzSpace l)
    (hL : L.toContinuousLinearMap = glyzCurveJetOperator γ a) :
    glyzTaylorCurve γ l a s = γ a + glyzTaylorMomentLinear L
      ((EuclideanSpace.equiv (Fin l) ℝ).symm (glyzMomentCurve l (s - a))) := by
  rw [glyzTaylorCurve_eq_sum]
  change _ = γ a + L.toContinuousLinearMap
    ((EuclideanSpace.equiv (Fin l) ℝ).symm
      (fun j => (((j : ℕ) + 1).factorial : ℝ)⁻¹ * (s - a) ^ ((j : ℕ) + 1)))
  rw [hL, glyzCurveJetOperator_apply]
  rfl

theorem iteratedDeriv_glyzTaylorCurve_affine_moment {l : ℕ}
    (γ : ℝ → GlyzSpace l) (a s : ℝ) (L : GlyzSpace l ≃L[ℝ] GlyzSpace l)
    (hL : L.toContinuousLinearMap = glyzCurveJetOperator γ a) (j : Fin l) :
    iteratedDeriv ((j : ℕ) + 1) (glyzTaylorCurve γ l a) s =
      glyzTaylorMomentLinear L (glyzEuclideanJetBlock l l (s - a) j) := by
  have hp : glyzTaylorCurve γ l a = fun u => γ a + glyzTaylorMomentLinear L
      ((EuclideanSpace.equiv (Fin l) ℝ).symm (glyzMomentCurve l (u - a))) :=
    funext fun u => glyzTaylorCurve_eq_affine_moment γ a u L hL
  rw [hp, iteratedDeriv_const_add (by omega)]
  have hs := iteratedDeriv_comp_sub_const (n := (j : ℕ) + 1)
    (f := fun u => glyzTaylorMomentLinear L
      ((EuclideanSpace.equiv (Fin l) ℝ).symm (glyzMomentCurve l u))) (s := a)
  rw [hs]
  exact iteratedDeriv_glyzMomentCurve_linear
    ((glyzTaylorMomentLinear L).toContinuousLinearMap.comp
      (EuclideanSpace.equiv (Fin l) ℝ).symm.toContinuousLinearMap) _ _

theorem glyzCurveBoxPoint_taylor_affine_moment {l : ℕ}
    (γ : ℝ → GlyzSpace l) (a s δ : ℝ) (L : GlyzSpace l ≃L[ℝ] GlyzSpace l)
    (hL : L.toContinuousLinearMap = glyzCurveJetOperator γ a) (v : Base l) :
    glyzCurveBoxPoint (glyzTaylorCurve γ l a) l s δ v = γ a +
      glyzTaylorMomentLinear L ((EuclideanSpace.equiv (Fin l) ℝ).symm
        (glyzMomentCurve l (s - a)) +
          ∑ j : Fin l, (δ ^ ((j : ℕ) + 1) * v j) • glyzEuclideanJetBlock l l (s - a) j) := by
  unfold glyzCurveBoxPoint
  rw [glyzTaylorCurve_eq_affine_moment γ a s L hL, map_add, map_sum]
  simp_rw [map_smul, iteratedDeriv_glyzTaylorCurve_affine_moment γ a s L hL]
  abel

end PlanarNikodym
