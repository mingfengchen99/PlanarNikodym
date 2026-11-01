import PlanarNikodym.Cells.StratumCompactProjectionExceptions

/-! From the original semianalytic germs, construct actual strata and one
closed definable null center exception for all strata of dimension below
two in a common compact window. General projected-rank strata are separate. -/
noncomputable section
open Set Metric MeasureTheory
namespace PlanarNikodym

theorem exists_local_semianalytic_strata_with_closed_null_projection_exception
    {n : ℕ} {J : Type} [Fintype J] (A : J → Set (Fin n → ℝ))
    (x₀ : Fin n → ℝ) (hA : ∀ j, SemianalyticAt (A j) x₀)
    (O : Set (Fin n → ℝ)) (hO : IsOpen O) (hxO : x₀ ∈ O)
    (L : (Fin n → ℝ) →L[ℝ] Base 2) :
    ∃ r : ℝ, 0 < r ∧ ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x₀ ∈ U ∧
      closure U ⊆ O ∧ closedBall x₀ r ⊆ U ∧
      ∃ (ι : Type) (_ : Fintype ι) (P : ι → AnalyticStratificationChart (Fin n → ℝ)),
        (⋃ i, (P i).image) = U ∧ Pairwise (fun i j => Disjoint (P i).image (P j).image) ∧
        (∀ i, LocallySemianalytic (P i).image) ∧ (∀ i, (P i).dim ≤ n) ∧
        (∀ i j, i ≠ j → ((P j).image ∩ closure (P i).image).Nonempty →
          (P j).image ⊆ closure (P i).image ∧ (P j).dim < (P i).dim) ∧
        (∀ j, A j ∩ U = ⋃ i : {i // (P i).image ⊆ A j}, (P i.val).image) ∧
        ∃ E : Set (Base 2), RanDefinable E ∧ IsClosed E ∧ volume E = 0 ∧
          ∀ i, (P i).dim < 2 → closure (L '' ((P i).image ∩ closedBall x₀ r)) ⊆ E := by
  obtain ⟨U, hU, hxU, hUO, hUsemi, ι, hι, P, hcover, hdisj, hsemi, hdim, hfront, hcomp⟩ :=
    exists_local_finite_semianalytic_stratification A x₀ hA (O ∩ ball x₀ 1)
      (hO.inter isOpen_ball) ⟨hxO, mem_ball_self zero_lt_one⟩
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
  let r := a / 2
  have hr : 0 < r := half_pos ha
  have hKU : closedBall x₀ r ⊆ U := (closedBall_subset_ball (half_lt_self ha)).trans hball
  have hbU : Bornology.IsBounded U := Metric.isBounded_ball.subset
    (fun x hx => (hUO (subset_closure hx)).2)
  have hPd (i : ι) : RanDefinable (P i).image := by
    apply (hsemi i).ranDefinable_of_bounded
    apply hbU.subset
    intro x hx
    rw [← hcover]
    exact mem_iUnion.mpr ⟨i, hx⟩
  have hKd : RanDefinable (closedBall x₀ r) := by
    rw [← closure_ball x₀ hr.ne']
    exact RanDefinable.closure (ranDefinable_ball x₀ r)
  have hE := finite_strata_compact_low_dimensional_exception P hcover hfront
    (closedBall x₀ r) (isCompact_closedBall _ _) hKU L
  refine ⟨r, hr, U, hU, hxU, (fun x hx => (hUO hx).1), hKU,
    ι, hι, P, hcover, hdisj, hsemi, hdim, hfront, hcomp,
    stratumCompactProjectionException P (closedBall x₀ r) L, ?_, hE⟩
  exact ranDefinable_stratumCompactProjectionException P hPd
    (closedBall x₀ r) (isCompact_closedBall _ _) hKd L

end PlanarNikodym
