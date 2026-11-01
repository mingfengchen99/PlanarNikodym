import PlanarNikodym.Analysis.Fourier.MomentConeGeometry
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Matrix.Normed

/-! Uniform stability of separated moment samples under perturbation.
The positive determinant bound and perturbation radius are constructed,
uniformly over all separated samples in the fixed time interval. -/
noncomputable section
open Set Metric
open scoped Matrix.Norms.Elementwise
namespace PlanarNikodym

def separatedMomentTimes (n : ℕ) (ν : ℝ) : Set (Aux (n + 1)) :=
  {t | (∀ i, t i ∈ Icc (-1 : ℝ) 1) ∧
    ∀ i j : Fin (n + 1), i < j → ν ≤ |t j - t i|}

theorem isCompact_separatedMomentTimes (n : ℕ) (ν : ℝ) :
    IsCompact (separatedMomentTimes n ν) := by
  have hb : IsCompact {t : Aux (n + 1) | ∀ i, t i ∈ Icc (-1 : ℝ) 1} := by
    simpa [Set.pi] using
      (isCompact_univ_pi (fun _ : Fin (n + 1) => isCompact_Icc (a := (-1 : ℝ)) (b := 1)))
  have hs : IsClosed {t : Aux (n + 1) |
      ∀ i j : Fin (n + 1), i < j → ν ≤ |t j - t i|} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le continuous_const (by fun_prop)
  exact hb.inter_right hs

theorem continuous_momentSamplingMatrix (n : ℕ) :
    Continuous (momentSamplingMatrix (n := n)) := by
  unfold momentSamplingMatrix momentCurve
  fun_prop

theorem exists_uniform_momentSampling_perturbation (n : ℕ) {ν : ℝ} (hν : 0 < ν) :
    ∃ b ε : ℝ, 0 < b ∧ 0 < ε ∧
      ∀ t ∈ separatedMomentTimes n ν,
        ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
          dist M (momentSamplingMatrix t) < ε → b ≤ |M.det| := by
  let b := momentFactorialConstant n * ∏ i : Fin (n + 1), ν ^ (Finset.Ioi i).card
  have hb : 0 < b := mul_pos (momentFactorialConstant_pos n)
    (Finset.prod_pos (fun _ _ => pow_pos hν _))
  let K := momentSamplingMatrix '' separatedMomentTimes n ν
  have hK : IsCompact K := (isCompact_separatedMomentTimes n ν).image
    (continuous_momentSamplingMatrix n)
  have ho : IsOpen {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ | b / 2 < |M.det|} :=
    isOpen_lt continuous_const continuous_id.matrix_det.abs
  have hsub : K ⊆ {M | b / 2 < |M.det|} := by
    rintro _ ⟨t, ht, rfl⟩
    exact (half_lt_self hb).trans_le
      (abs_det_momentSamplingMatrix_lower_bound t hν.le ht.2)
  obtain ⟨ε, hε, hstable⟩ := hK.exists_thickening_subset_open ho hsub
  refine ⟨b / 2, ε, half_pos hb, hε, ?_⟩
  intro t ht M hM
  exact (hstable (mem_thickening_iff.mpr ⟨momentSamplingMatrix t, ⟨t, ht, rfl⟩, hM⟩)).le

end PlanarNikodym
