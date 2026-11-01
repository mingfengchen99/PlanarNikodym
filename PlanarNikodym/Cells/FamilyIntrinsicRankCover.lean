import PlanarNikodym.Rank.FiniteIntrinsicRankCover
import PlanarNikodym.Geometry.Cinematic
import PlanarNikodym.Geometry.SemianalyticCoordinateBalls

/-! The finite intrinsic-rank construction applied to actual function
derivatives and to the original Family curves in fixed linear parameter
coordinates. No supplied tangent frame, rank minor or stratification is
an assumption of these existence theorems. -/
noncomputable section
open Set Module
namespace PlanarNikodym

theorem LocallySemianalytic.exists_finite_function_intrinsic_rank_cover
    {n z : ℕ} {X : Type} {S : Set (Fin n → ℝ)}
    (hS : LocallySemianalytic S) (hb : Bornology.IsBounded S)
    (O : Set (Fin n → ℝ)) (hO : IsOpen O) (hSO : closure S ⊆ O)
    (f : X → (Fin n → ℝ) → ℝ) (hf : ∀ t, AnalyticOnNhd ℝ (f t) O)
    (L : (Fin n → ℝ) →L[ℝ] (Fin z → ℝ)) :
    ∃ (ι : Type) (_ : Fintype ι)
      (P : ι → IntrinsicRankChart O (functionDerivative f) L),
      (⋃ i, (P i).chart.image) = S := by
  apply hS.exists_finite_intrinsic_rank_chart_cover hb O hO hSO (functionDerivative f) L
  intro j t x hx
  exact ((ContinuousLinearMap.apply ℝ ℝ (Pi.single j 1)).analyticAt _).comp (hf t x hx).fderiv

def Family.coordinateFunctionDerivative {d : ℕ} (G : Family 2 d) :
    (Fin (d + 2) → ℝ) → (Fin (d + 2) → ℝ) →ₗ[ℝ] (G.I.carrier → ℝ) :=
  functionDerivative (fun (t : G.I.carrier) x => G.γ t (parameterFrame d x))

def parameterCenterDerivative (d : ℕ) :
    (Fin (d + 2) → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  (ContinuousLinearMap.fst ℝ (Base 2) (Aux d)).comp (parameterFrame d).toContinuousLinearMap

theorem Family.exists_finite_intrinsic_rank_cover {d : ℕ} (G : Family 2 d)
    (ho : IsOpen G.W) (ha : G.IsAnalytic)
    (S : Set (Fin (d + 2) → ℝ)) (hS : LocallySemianalytic S)
    (hb : Bornology.IsBounded S) (hSW : closure S ⊆ (parameterFrame d) ⁻¹' G.W) :
    ∃ (ι : Type) (_ : Fintype ι)
      (P : ι → IntrinsicRankChart ((parameterFrame d) ⁻¹' G.W)
        G.coordinateFunctionDerivative (parameterCenterDerivative d)),
      (⋃ i, (P i).chart.image) = S := by
  apply hS.exists_finite_function_intrinsic_rank_cover hb ((parameterFrame d) ⁻¹' G.W)
    (ho.preimage (parameterFrame d).continuous) hSW
    (fun (t : G.I.carrier) x => G.γ t (parameterFrame d x)) ?_ (parameterCenterDerivative d)
  intro t x hx
  exact (G.parameter_analytic ha (parameterFrame d x) hx t).comp ((parameterFrame d).analyticAt x)

theorem Family.exists_finite_intrinsic_rank_ball_cover {d : ℕ} (G : Family 2 d)
    (ho : IsOpen G.W) (ha : G.IsAnalytic) (c : Fin (d + 2) → ℝ) (r : ℝ) (hr : 0 < r)
    (hball : closure (Metric.ball c r) ⊆ (parameterFrame d) ⁻¹' G.W) :
    ∃ (ι : Type) (_ : Fintype ι)
      (P : ι → IntrinsicRankChart ((parameterFrame d) ⁻¹' G.W)
        G.coordinateFunctionDerivative (parameterCenterDerivative d)),
      (⋃ i, (P i).chart.image) = Metric.ball c r :=
  G.exists_finite_intrinsic_rank_cover ho ha (Metric.ball c r)
    (locallySemianalytic_coordinate_ball c r hr) Metric.isBounded_ball hball

end PlanarNikodym
