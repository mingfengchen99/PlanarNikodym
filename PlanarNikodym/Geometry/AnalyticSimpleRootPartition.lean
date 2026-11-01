import PlanarNikodym.Geometry.AnalyticCylindricalPartition
import PlanarNikodym.Geometry.AnalyticOrderedSimpleRoots
import PlanarNikodym.Geometry.CompactFiberNeighborhood
import Mathlib.Analysis.Normed.Module.Connected

/-! Actual finite analytic cylindrical sign partitions near a compact simple-root
fiber. The root atlas and the common analytic tube are both constructed from the
original fiber hypotheses. No root-covering input is assumed. -/

noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A compact fiber with nonzero endpoints and only simple interior zeros admits
exactly `2n+1` distinct connected analytic graph/band cells on one open parameter
ball. They partition the whole cylinder; the function vanishes on the graph cells
and has one strict sign on each band cell. This theorem does not treat root collisions. -/
theorem exists_analytic_simple_root_cylindrical_partition
    (f : E × ℝ → ℝ) (x₀ : E) (A B : ℝ) (hAB : A < B)
    (hf : ∀ t ∈ Icc A B, AnalyticAt ℝ f (x₀, t))
    (hA : f (x₀, A) ≠ 0) (hB : f (x₀, B) ≠ 0)
    (hd : ∀ t ∈ Ioo A B, f (x₀, t) = 0 →
      deriv (fun s => f (x₀, s)) t ≠ 0) :
    ∃ (n : ℕ) (ε : ℝ), 0 < ε ∧ ∃ ρ : Fin n → E → ℝ,
      (∀ i, AnalyticOnNhd ℝ (ρ i) (Metric.ball x₀ ε)) ∧
      (∀ x ∈ Metric.ball x₀ ε, StrictMono (fun i => ρ i x)) ∧
      (∀ x ∈ Metric.ball x₀ ε, ∀ i, ρ i x ∈ Ioo A B) ∧
      AnalyticOnNhd ℝ f (Metric.ball x₀ ε ×ˢ Icc A B) ∧
      (∀ x ∈ Metric.ball x₀ ε, ∀ t ∈ Ioo A B,
        f (x, t) = 0 ↔ ∃ i, t = ρ i x) ∧
      (⋃ i, analyticCylindricalCell (Metric.ball x₀ ε) (analyticRootCuts A B ρ) i) =
        Metric.ball x₀ ε ×ˢ Ioo A B ∧
      Pairwise (fun i j =>
        Disjoint (analyticCylindricalCell (Metric.ball x₀ ε) (analyticRootCuts A B ρ) i)
          (analyticCylindricalCell (Metric.ball x₀ ε) (analyticRootCuts A B ρ) j)) ∧
      (∀ i, IsConnected
        (analyticCylindricalCell (Metric.ball x₀ ε) (analyticRootCuts A B ρ) i)) ∧
      (Set.range (analyticCylindricalCell (Metric.ball x₀ ε)
        (analyticRootCuts A B ρ))).ncard = 2 * n + 1 ∧
      (∀ (i : Fin n) z,
        z ∈ analyticCylindricalCell (Metric.ball x₀ ε) (analyticRootCuts A B ρ) (Sum.inl i) →
        f z = 0) ∧
      (∀ i : Fin (n + 1),
        (∀ z ∈ analyticCylindricalCell (Metric.ball x₀ ε) (analyticRootCuts A B ρ)
          (Sum.inr i), f z < 0) ∨
        (∀ z ∈ analyticCylindricalCell (Metric.ball x₀ ε) (analyticRootCuts A B ρ)
          (Sum.inr i), 0 < f z)) := by
  obtain ⟨n, ε₀, hε₀, ρ, hρa, hρo, hρb, hroot⟩ :=
    exists_ordered_analytic_simple_root_branches f x₀ A B hAB hf hA hB hd
  obtain ⟨V, hV, hxV, hVa⟩ := exists_open_nhds_compact_fiber_property
    (fun z => AnalyticAt ℝ f z) x₀ (Icc A B) isCompact_Icc
    (fun t ht => (hf t ht).eventually_analyticAt)
  have hnb : V ∩ Metric.ball x₀ ε₀ ∈ 𝓝 x₀ :=
    (hV.inter Metric.isOpen_ball).mem_nhds ⟨hxV, Metric.mem_ball_self hε₀⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnb
  have hsub : Metric.ball x₀ ε ⊆ Metric.ball x₀ ε₀ :=
    fun _ hx => (hball hx).2
  have ha : ∀ i, AnalyticOnNhd ℝ (ρ i) (Metric.ball x₀ ε) :=
    fun i => (hρa i).mono hsub
  have ho : ∀ x ∈ Metric.ball x₀ ε, StrictMono (fun i => ρ i x) :=
    fun x hx => hρo x (hsub hx)
  have hb : ∀ x ∈ Metric.ball x₀ ε, ∀ i, ρ i x ∈ Ioo A B :=
    fun x hx => hρb x (hsub hx)
  have hfa : AnalyticOnNhd ℝ f (Metric.ball x₀ ε ×ˢ Icc A B) :=
    fun z hz => hVa z.1 (hball hz.1).1 z.2 hz.2
  have hz : ∀ x ∈ Metric.ball x₀ ε, ∀ t ∈ Ioo A B,
      f (x, t) = 0 ↔ ∃ i, t = ρ i x :=
    fun x hx => hroot x (hsub hx)
  have hU : IsConnected (Metric.ball x₀ ε) := Metric.isConnected_ball hε
  obtain ⟨hcover, hdisj, hconn⟩ := analytic_ordered_root_partition A B ρ hAB hU ha ho hb
  have hcard := ncard_range_analyticCylindricalCell (analyticRootCuts A B ρ) hU
    (analyticOnNhd_analyticRootCuts A B ρ ha) (strictMono_analyticRootCuts A B ρ hAB ho hb)
  have hfc : ContinuousOn f (Metric.ball x₀ ε ×ˢ Ioo A B) :=
    hfa.continuousOn.mono (fun _ hz => ⟨hz.1, hz.2.1.le, hz.2.2.le⟩)
  obtain ⟨hzero, hsign⟩ :=
    analytic_ordered_root_sign_partition A B ρ hAB hU ha ho hb f hfc hz
  exact ⟨n, ε, hε, ρ, ha, ho, hb, hfa, hz, hcover, hdisj, hconn, hcard, hzero, hsign⟩

end PlanarNikodym
