import PlanarNikodym.Tame.DefinableOrderedThomPartition
import PlanarNikodym.Tame.CompactAnalyticGraphs

/-! A local complete ordered root partition constructed from one actual
analytic coefficient germ. Neither definability, discriminant nonvanishing,
constant multiplicity nor a root list is assumed. -/
noncomputable section
open Set Filter Polynomial Metric
open scoped Topology
namespace PlanarNikodym

theorem exists_local_analytic_thom_root_partition {d m : ℕ}
    (a : (Fin d → ℝ) → Fin m → ℝ) (x₀ : Fin d → ℝ) (ha : AnalyticAt ℝ a x₀) :
    ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧
      AnalyticOnNhd ℝ a (closedBall x₀ ε) ∧
      (∀ j, RanDefinableOn (fun x => a x j) (ball x₀ ε)) ∧
      (∀ x ∈ ball x₀ ε, ∀ t, (weierstrassPolynomial (a x)).eval t = 0 → |t| < R) ∧
      let U := ball x₀ ε
      (⋃ i : PolynomialOrderedThomIndex m, polynomialThomBaseCell a U i) = U ∧
      Pairwise (fun i j : PolynomialOrderedThomIndex m =>
        Disjoint (polynomialThomBaseCell a U i) (polynomialThomBaseCell a U j)) ∧
      ∀ i : PolynomialOrderedThomIndex m,
        RanDefinable (polynomialThomBaseCell a U i) ∧
        (∀ k, ContinuousOn (polynomialThomRoot a (i.2 k)) (polynomialThomBaseCell a U i)) ∧
        (∀ k, RanDefinableOn (polynomialThomRoot a (i.2 k)) (polynomialThomBaseCell a U i)) ∧
        ∀ x ∈ polynomialThomBaseCell a U i,
          StrictMono (fun k => polynomialThomRoot a (i.2 k) x) ∧
          ∀ t : ℝ, (weierstrassPolynomial (a x)).eval t = 0 ↔
            ∃ k, t = polynomialThomRoot a (i.2 k) x := by
  classical
  obtain ⟨r, hr, hanalytic⟩ := ha.exists_ball_analyticOnNhd
  obtain ⟨W, R, hW, hxW, hR, hbound⟩ :=
    exists_open_nhds_uniform_weierstrass_root_bound a x₀ ha.continuousAt
  have hchoice (j : Fin m) : ∃ V : Set (Fin d → ℝ), IsOpen V ∧ x₀ ∈ V ∧
      RanDefinableOn (fun x => a x j) V := by
    obtain ⟨V, ho, hsub, _, hd⟩ := exists_ranDefinableOn_nhds_of_compact
      (isCompact_singleton : IsCompact ({x₀} : Set (Fin d → ℝ)))
      (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst x
          exact analyticAt_pi_iff.mp ha j)
    exact ⟨V, ho, hsub (mem_singleton x₀), hd⟩
  choose V hV hxV hdV using hchoice
  have hnear : {x | x ∈ ball x₀ r ∧ x ∈ W ∧ ∀ j, x ∈ V j} ∈ 𝓝 x₀ := by
    filter_upwards [ball_mem_nhds x₀ hr, hW.mem_nhds hxW,
      Filter.eventually_all.mpr (fun j => (hV j).mem_nhds (hxV j))] with x hx hw hv
    exact ⟨hx, hw, hv⟩
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp hnear
  let ε := δ / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hcl : closedBall x₀ ε ⊆ ball x₀ δ := by
    intro x hx
    rw [mem_closedBall] at hx
    rw [mem_ball]
    dsimp [ε] at hx
    linarith
  have han : AnalyticOnNhd ℝ a (closedBall x₀ ε) :=
    fun x hx => hanalytic x (hb (hcl hx)).1
  have hda (j : Fin m) : RanDefinableOn (fun x => a x j) (ball x₀ ε) :=
    (hdV j).restrict (ranDefinable_ball x₀ ε)
      (fun _ hx => (hb (hcl (ball_subset_closedBall hx))).2.2 j)
  refine ⟨ε, R, hε, hR, han, hda, ?_, ?_⟩
  · intro x hx t ht
    exact hbound x (hb (hcl (ball_subset_closedBall hx))).2.1 t ht
  · exact finite_continuous_definable_polynomial_root_partition a (ball x₀ ε)
      isOpen_ball (ranDefinable_ball x₀ ε) (han.mono ball_subset_closedBall).continuousOn hda

end PlanarNikodym
