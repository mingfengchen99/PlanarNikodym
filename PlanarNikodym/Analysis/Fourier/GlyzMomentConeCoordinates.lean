import PlanarNikodym.Analysis.Fourier.GlyzProjectiveChart
import PlanarNikodym.Analysis.Fourier.GlyzOscillatoryConeDecoupling
import PlanarNikodym.Analysis.Fourier.MomentConeGeometry

/-! Exact coordinates between the polynomial Taylor phase and the
unnormalized moment cone. All factorials and the constant coefficient
are retained; the curve's torsion and derivative bounds are constructed. -/
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators ContDiff RealInnerProductSpace
namespace PlanarNikodym

def glyzEuclideanMomentCurve (k : ℕ) (t : ℝ) : GlyzSpace k :=
  (EuclideanSpace.equiv (Fin k) ℝ).symm (glyzMomentCurve k t)

theorem contDiff_glyzEuclideanMomentCurve (k : ℕ) :
    ContDiff ℝ ∞ (glyzEuclideanMomentCurve k) :=
  (EuclideanSpace.equiv (Fin k) ℝ).symm.contDiff.comp
    (contDiff_pi.mpr fun _ => contDiff_id.pow _)

theorem glyzEuclideanMomentCurve_jet_frame (k : ℕ) (t : ℝ) :
    (glyzCurveJetOperator (glyzEuclideanMomentCurve k) t).toLinearMap =
      (glyzMomentFrequencyFrame k t 1 zero_lt_one).toLinearMap := by
  apply (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.ext
  intro j
  change glyzCurveJetOperator (glyzEuclideanMomentCurve k) t
    (EuclideanSpace.basisFun (Fin k) ℝ j) =
      glyzMomentFrequencyFrame k t 1 zero_lt_one (EuclideanSpace.basisFun (Fin k) ℝ j)
  rw [glyzCurveJetOperator_basis, glyzMomentFrequencyFrame_basis, one_pow, one_smul]
  exact iteratedDeriv_glyzMomentCurve_linear
    (EuclideanSpace.equiv (Fin k) ℝ).symm.toContinuousLinearMap ((j : ℕ) + 1) t

theorem det_glyzEuclideanMomentCurve_jet_ne_zero (k : ℕ) (t : ℝ) :
    (glyzCurveJetOperator (glyzEuclideanMomentCurve k) t).det ≠ 0 := by
  change LinearMap.det (glyzCurveJetOperator (glyzEuclideanMomentCurve k) t).toLinearMap ≠ 0
  rw [glyzEuclideanMomentCurve_jet_frame]
  exact (LinearEquiv.isUnit_det' (glyzMomentFrequencyFrame k t 1 zero_lt_one).toLinearEquiv).ne_zero

theorem exists_glyzEuclideanMomentCurve_bounds (k : ℕ) :
    ∃ β B : ℝ, 0 < β ∧ 0 < B ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ j ≤ k + 1,
        ‖iteratedDeriv j (glyzEuclideanMomentCurve k) t‖ ≤ B) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        β ≤ |(glyzCurveJetOperator (glyzEuclideanMomentCurve k) t).det| := by
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1))
    (continuous_glyzCurveJetOperator_det _ (contDiff_glyzEuclideanMomentCurve k)).abs.continuousOn
  obtain ⟨B, hB, hb⟩ := exists_glyz_curve_derivative_bound_closedBall
    (glyzEuclideanMomentCurve k) (contDiff_glyzEuclideanMomentCurve k) 0 1 (k + 1)
  refine ⟨|(glyzCurveJetOperator (glyzEuclideanMomentCurve k) t).det|, B,
    abs_pos.mpr (det_glyzEuclideanMomentCurve_jet_ne_zero k t), hB, ?_, hmin⟩
  intro s hs j hj
  apply hb s ?_ j hj
  simpa only [mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg hs.1] using hs.2

/-- The zero-th coefficient is radial; coefficient j+1 carries (j+1)!
so the Taylor polynomial pairs with (t,t²,...,t^k,1). -/
def glyzMomentConeCoefficientEquiv (k : ℕ) : GlyzConeSpace k ≃L[ℝ] Aux (k + 1) :=
  ((glyzConeToJetEquiv k).trans (EuclideanSpace.equiv (Fin (k + 1)) ℝ)).trans
    (coefficientDilation (fun j : Fin (k + 1) => ((j : ℕ).factorial : ℝ))
      (fun _ => by positivity))

@[simp] theorem glyzMomentConeCoefficientEquiv_zero (k : ℕ) (x : GlyzConeSpace k) :
    glyzMomentConeCoefficientEquiv k x 0 = (WithLp.ofLp x).2 := by
  simp [glyzMomentConeCoefficientEquiv, coefficientDilation, glyzConeToJetEquiv,
    glyzConeToJetLinearEquiv]

@[simp] theorem glyzMomentConeCoefficientEquiv_succ (k : ℕ) (x : GlyzConeSpace k) (j : Fin k) :
    glyzMomentConeCoefficientEquiv k x j.succ =
      (((j : ℕ) + 1).factorial : ℝ) * (WithLp.ofLp x).1 j := by
  rfl

theorem jetPolynomial_glyzMomentConeCoefficientEquiv (k : ℕ) (x : GlyzConeSpace k) (t : ℝ) :
    jetPolynomial (glyzMomentConeCoefficientEquiv k x) t =
      inner ℝ x (WithLp.toLp 2 (glyzEuclideanMomentCurve k t, (1 : ℝ))) := by
  unfold jetPolynomial
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
    mul_one, div_one, glyzMomentConeCoefficientEquiv_zero,
    glyzMomentConeCoefficientEquiv_succ, Fin.val_succ]
  have hterm (j : Fin k) :
      (((((j : ℕ) + 1).factorial : ℝ) * (WithLp.ofLp x).1 j) * t ^ ((j : ℕ) + 1)) /
        (((j : ℕ) + 1).factorial : ℝ) = (WithLp.ofLp x).1 j * t ^ ((j : ℕ) + 1) := by
    field_simp
  simp_rw [hterm]
  rw [WithLp.prod_inner_apply]
  change (WithLp.ofLp x).2 + ∑ j : Fin k, (WithLp.ofLp x).1 j * t ^ ((j : ℕ) + 1) =
    (∑ j : Fin k, t ^ ((j : ℕ) + 1) * (WithLp.ofLp x).1 j) + 1 * (WithLp.ofLp x).2
  simp only [mul_comm]
  ring

theorem frequency_jetPolynomial_glyzMomentConeCoefficientEquiv
    (k : ℕ) (x : GlyzConeSpace k) (t η R : ℝ) :
    R * η * jetPolynomial (glyzMomentConeCoefficientEquiv k x) t =
      inner ℝ x (glyzCurveConeFrequency k (glyzEuclideanMomentCurve k) R (t, η)) := by
  rw [jetPolynomial_glyzMomentConeCoefficientEquiv]
  have he : WithLp.toLp 2 (η • glyzEuclideanMomentCurve k t, η) =
      η • WithLp.toLp 2 (glyzEuclideanMomentCurve k t, (1 : ℝ)) := by
    apply WithLp.ofLp_injective
    simp only [WithLp.ofLp_smul, Prod.smul_mk, smul_eq_mul, mul_one]
  simp only [glyzCurveConeFrequency, he, inner_smul_right]
  ring

end PlanarNikodym
