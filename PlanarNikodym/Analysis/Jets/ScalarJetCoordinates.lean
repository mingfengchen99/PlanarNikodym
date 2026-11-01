import PlanarNikodym.Analysis.Jets.AverageHigherDerivatives

/-! The actual auxiliary multilinear operator norm is controlled by its
finitely many scalar coordinate evaluations. -/
noncomputable section
open scoped BigOperators
namespace PlanarNikodym

/-- The standard coordinate vector in the auxiliary parameter space. -/
def scalarJetBasis {d : ℕ} (a : Fin d) : Aux d := Pi.single a 1

/-- No vector-valued smoothing theorem is needed: finitely many actual
coordinate evaluations control the complete auxiliary jet. -/
theorem scalarJet_norm_le_sum_coordinates {d j : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : Aux d [×j]→L[ℝ] F) :
    ‖T‖ ≤ ∑ α : Fin j → Fin d, ‖T (fun i => scalarJetBasis (α i))‖ := by
  classical
  apply T.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  have hv (i : Fin j) : v i = ∑ a : Fin d, (v i a) • scalarJetBasis a := by
    ext a
    simp [scalarJetBasis, Pi.single_apply]
  calc
    ‖T v‖ = ‖T (fun i => ∑ a : Fin d, (v i a) • scalarJetBasis a)‖ := by
      congr 2
      funext i
      exact hv i
    _ = ‖∑ α : Fin j → Fin d,
        (∏ i, v i (α i)) • T (fun i => scalarJetBasis (α i))‖ := by
      change ‖T.toMultilinearMap (fun i => ∑ a : Fin d, (v i a) • scalarJetBasis a)‖ = _
      rw [T.toMultilinearMap.map_sum]
      change ‖∑ α : Fin j → Fin d, T (fun i => (v i (α i)) • scalarJetBasis (α i))‖ = _
      simp only [T.map_smul_univ]
    _ ≤ ∑ α : Fin j → Fin d,
        ‖(∏ i, v i (α i)) • T (fun i => scalarJetBasis (α i))‖ := norm_sum_le _ _
    _ ≤ ∑ α : Fin j → Fin d,
        (∏ i, ‖v i‖) * ‖T (fun i => scalarJetBasis (α i))‖ := by
      apply Finset.sum_le_sum
      intro α _
      rw [norm_smul, norm_prod]
      gcongr with i _
      exact norm_le_pi_norm (v i) (α i)
    _ = (∑ α : Fin j → Fin d, ‖T (fun i => scalarJetBasis (α i))‖) *
        ∏ i, ‖v i‖ := by rw [← Finset.mul_sum, mul_comm]

end PlanarNikodym
