import PlanarNikodym.Analysis.Fourier.MixedTaylorJets
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Matrix.Normed

/-! Mixed derivatives at two distinct centers. The matrix is constructed
from actual polynomial derivatives, rather than from a transversality input. -/
noncomputable section
open Set Metric Polynomial
open scoped Matrix.Norms.Elementwise
namespace PlanarNikodym

def mixedJetFlatten (l r : ℕ) : (Aux l × Aux r) ≃ₗ[ℝ] Aux (l + r) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin l) (Fin r) ℝ ℝ).symm.trans
    (LinearEquiv.piCongrLeft ℝ (fun _ : Fin (l + r) => ℝ) finSumFinEquiv)

def mixedDerivativeJetMap (l r : ℕ) (s t : ℝ) :
    Polynomial.degreeLT ℝ (l + r) →ₗ[ℝ] (Aux l × Aux r) :=
  ((coefficientDilation (fun j : Fin l => ((j : ℕ).factorial : ℝ))
      (by intro j; positivity)).toLinearMap.prodMap
    (coefficientDilation (fun j : Fin r => ((j : ℕ).factorial : ℝ))
      (by intro j; positivity)).toLinearMap).comp (mixedTaylorJetMap l r s t)

theorem mixedDerivativeJetMap_apply_left (l r : ℕ) (s t : ℝ)
    (p : Polynomial.degreeLT ℝ (l + r)) (j : Fin l) :
    (mixedDerivativeJetMap l r s t p).1 j =
      iteratedDeriv j (fun x => p.1.eval x) s := by
  exact (iteratedDeriv_polynomial_eval_eq_taylor p.1 j s).symm

theorem mixedDerivativeJetMap_apply_right (l r : ℕ) (s t : ℝ)
    (p : Polynomial.degreeLT ℝ (l + r)) (j : Fin r) :
    (mixedDerivativeJetMap l r s t p).2 j =
      iteratedDeriv j (fun x => p.1.eval x) t := by
  exact (iteratedDeriv_polynomial_eval_eq_taylor p.1 j t).symm

theorem mixedDerivativeJetMap_injective (l r : ℕ) {s t : ℝ} (hst : s ≠ t) :
    Function.Injective (mixedDerivativeJetMap l r s t) := by
  intro p q hpq
  apply mixedTaylorJetMap_injective l r hst
  apply Prod.ext
  · ext j
    exact mul_left_cancel₀ (by positivity : ((j : ℕ).factorial : ℝ) ≠ 0)
      (congrFun (congrArg Prod.fst hpq) j)
  · ext j
    exact mul_left_cancel₀ (by positivity : ((j : ℕ).factorial : ℝ) ≠ 0)
      (congrFun (congrArg Prod.snd hpq) j)

def mixedDerivativeMatrix (l r : ℕ) (s t : ℝ) :
    Matrix (Fin (l + r)) (Fin (l + r)) ℝ :=
  LinearMap.toMatrix' ((mixedJetFlatten l r).toLinearMap.comp
    ((mixedDerivativeJetMap l r s t).comp (Polynomial.degreeLTEquiv ℝ (l + r)).symm.toLinearMap))

theorem det_mixedDerivativeMatrix_ne_zero (l r : ℕ) {s t : ℝ} (hst : s ≠ t) :
    (mixedDerivativeMatrix l r s t).det ≠ 0 := by
  rw [mixedDerivativeMatrix, LinearMap.det_toMatrix']
  intro h
  apply LinearMap.det_eq_zero_iff_ker_ne_bot.mp h
  apply LinearMap.ker_eq_bot.mpr
  exact (mixedJetFlatten l r).injective.comp
    ((mixedDerivativeJetMap_injective l r hst).comp
      (Polynomial.degreeLTEquiv ℝ (l + r)).symm.injective)

theorem continuous_mixedDerivativeMatrix (l r : ℕ) :
    Continuous (fun z : ℝ × ℝ => mixedDerivativeMatrix l r z.1 z.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun z : ℝ × ℝ => mixedJetFlatten l r
    (mixedDerivativeJetMap l r z.1 z.2
      ((Polynomial.degreeLTEquiv ℝ (l + r)).symm (Pi.single j 1))) i)
  apply (continuous_apply i).comp
  apply (mixedJetFlatten l r).toContinuousLinearEquiv.continuous.comp
  apply Continuous.prodMk
  · apply continuous_pi
    intro k
    change Continuous (fun z : ℝ × ℝ => ((k : ℕ).factorial : ℝ) *
      (Polynomial.taylor z.1 ((Polynomial.degreeLTEquiv ℝ (l + r)).symm
        (Pi.single j 1)).1).coeff k)
    simp_rw [Polynomial.taylor_coeff]
    fun_prop
  · apply continuous_pi
    intro k
    change Continuous (fun z : ℝ × ℝ => ((k : ℕ).factorial : ℝ) *
      (Polynomial.taylor z.2 ((Polynomial.degreeLTEquiv ℝ (l + r)).symm
        (Pi.single j 1)).1).coeff k)
    simp_rw [Polynomial.taylor_coeff]
    fun_prop

def separatedMixedCenters (ν : ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 ∈ Icc (-1 : ℝ) 1 ∧ z.2 ∈ Icc (-1 : ℝ) 1 ∧ ν ≤ |z.1 - z.2|}

theorem isCompact_separatedMixedCenters (ν : ℝ) :
    IsCompact (separatedMixedCenters ν) := by
  have he : separatedMixedCenters ν = (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ∩
      {z : ℝ × ℝ | ν ≤ |z.1 - z.2|} := by
    ext z
    simp [separatedMixedCenters, Prod.le_def, and_assoc, and_left_comm, and_comm]
  rw [he]
  exact (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_const ((continuous_fst.sub continuous_snd).abs))

/-- Uniform mixed-derivative transversality on separated compact centers,
including a uniform neighborhood of perturbation matrices. -/
theorem exists_uniform_mixedDerivative_perturbation (l r : ℕ) {ν : ℝ} (hν : 0 < ν) :
    ∃ b ε : ℝ, 0 < b ∧ 0 < ε ∧
      ∀ z ∈ separatedMixedCenters ν,
        ∀ M : Matrix (Fin (l + r)) (Fin (l + r)) ℝ,
          dist M (mixedDerivativeMatrix l r z.1 z.2) < ε → b ≤ |M.det| := by
  let K := (fun z : ℝ × ℝ => mixedDerivativeMatrix l r z.1 z.2) ''
    separatedMixedCenters ν
  have hK : IsCompact K := (isCompact_separatedMixedCenters ν).image
    (continuous_mixedDerivativeMatrix l r)
  have hn : ∀ M ∈ K, 0 < |M.det| := by
    rintro _ ⟨z, hz, rfl⟩
    apply abs_pos.mpr (det_mixedDerivativeMatrix_ne_zero l r ?_)
    intro he
    have : ν ≤ 0 := by simpa [he] using hz.2.2
    exact (not_le_of_gt hν) this
  by_cases he : K.Nonempty
  · obtain ⟨M₀, hM₀, hmin⟩ := hK.exists_isMinOn he continuous_id.matrix_det.abs.continuousOn
    have hb := hn M₀ hM₀
    have ho : IsOpen {M : Matrix (Fin (l + r)) (Fin (l + r)) ℝ |
        |M₀.det| / 2 < |M.det|} :=
      isOpen_lt continuous_const continuous_id.matrix_det.abs
    obtain ⟨ε, hε, hstable⟩ := hK.exists_thickening_subset_open ho
      (fun M hM => (half_lt_self hb).trans_le (hmin hM))
    refine ⟨|M₀.det| / 2, ε, half_pos hb, hε, ?_⟩
    intro z hz M hM
    exact (hstable (mem_thickening_iff.mpr
      ⟨mixedDerivativeMatrix l r z.1 z.2, ⟨z, hz, rfl⟩, hM⟩)).le
  · refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
    intro z hz
    exact (he ⟨_, ⟨z, hz, rfl⟩⟩).elim

end PlanarNikodym
