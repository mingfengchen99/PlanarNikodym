import PlanarNikodym.Rank.RankRegularity

noncomputable section
open Set Submodule Module
namespace PlanarNikodym

/-- A finite evaluation minor retains the selected original columns and
evaluation times. These data can be passed to a compatible cell theorem;
an arbitrary analytic function on an open bounded set would not suffice. -/
structure EvaluationMinor (n : ℕ) (X : Type*) where
  size : ℕ
  column : Fin size → Fin n
  time : Fin size → X

def EvaluationMinor.value {n : ℕ} {X E : Type*} (M : EvaluationMinor n X)
    (f : Fin n → X → E → ℝ) (x : E) : ℝ :=
  Matrix.det (fun i j => f (M.column j) (M.time i) x)

theorem EvaluationMinor.analytic {n : ℕ} {X E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (M : EvaluationMinor n X)
    (f : Fin n → X → E → ℝ) (W : Set E)
    (hf : ∀ j t, AnalyticOnNhd ℝ (f j t) W) :
    AnalyticOnNhd ℝ (M.value f) W :=
  fun x hx => analyticAt_det (fun i j => hf (M.column j) (M.time i) x hx)

/-- Generic rank with the actual finite minor exposed, including rank zero
(the empty determinant). -/
theorem generic_rank_evaluation_minor {E X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (f : Fin n → X → E → ℝ) (W : Set E) (hW : IsOpen W)
    (hne : W.Nonempty) (hconn : IsPreconnected W)
    (hf : ∀ j t, AnalyticOnNhd ℝ (f j t) W) :
    ∃ M : EvaluationMinor n X, M.size ≤ n ∧
      (∃ q ∈ W, M.value f q ≠ 0) ∧
      IsOpen {x | x ∈ W ∧ M.value f x ≠ 0} ∧
      W ⊆ closure {x | x ∈ W ∧ M.value f x ≠ 0} ∧
      (∀ x ∈ W, finrank ℝ (span ℝ (range (fun j t => f j t x))) ≤ M.size) ∧
      ∀ x ∈ W, M.value f x ≠ 0 →
        finrank ℝ (span ℝ (range (fun j t => f j t x))) = M.size := by
  classical
  let r (x : E) := finrank ℝ (span ℝ (range (fun j t => f j t x)))
  have hr (x : E) : r x ≤ n := by
    simpa only [r, Set.finrank, Fintype.card_fin] using
      finrank_range_le_card (R := ℝ) (fun j t => f j t x)
  have hfinite : (r '' W).Finite := (finite_Iic n).subset (by
    rintro _ ⟨x, _, rfl⟩; exact hr x)
  obtain ⟨m, hm, hmax⟩ := (r '' W).exists_max_image id hfinite (hne.image r)
  obtain ⟨q, hq, hqm⟩ := hm
  subst m
  obtain ⟨σ, hσ⟩ := select_independent_generators (fun j t => f j t q)
  obtain ⟨t, ht⟩ := exists_eval_det_ne_zero (fun j s => f (σ j) s q) hσ
  let M : EvaluationMinor n X := ⟨r q, σ, t⟩
  have hMq : M.value f q ≠ 0 := ht
  obtain ⟨hDo, hDd⟩ := analytic_nonzero_locus W hW hconn (M.value f)
    (M.analytic f W hf) q hq hMq
  refine ⟨M, hr q, ⟨q, hq, hMq⟩, hDo, hDd, ?_, ?_⟩
  · intro x hx
    exact hmax (r x) (mem_image_of_mem r hx)
  · intro x hx hMx
    apply le_antisymm (hmax (r x) (mem_image_of_mem r hx))
    have hli := independent_of_eval_det_ne_zero (fun j s => f (σ j) s x) t hMx
    have hle : span ℝ (range (fun j s => f (σ j) s x)) ≤
        span ℝ (range (fun j s => f j s x)) := span_mono (by
      rintro _ ⟨j, rfl⟩; exact mem_range_self (σ j))
    haveI := FiniteDimensional.span_of_finite ℝ (finite_range (fun j s => f j s x))
    have hdim := Submodule.finrank_mono hle
    rw [finrank_span_eq_card hli, Fintype.card_fin] at hdim
    exact hdim

structure DoubleRankMinor {d : ℕ} (G : Family 2 d) where
  point : EvaluationMinor d G.I.carrier
  curve : EvaluationMinor (d + 2) G.I.carrier

def DoubleRankMinor.regularSet {d : ℕ} {G : Family 2 d} (M : DoubleRankMinor G) :
    Set (Parameters 2 d) :=
  {p | p ∈ G.W ∧ M.point.value (fun j t p => G.uColumn p j t) p ≠ 0 ∧
    M.curve.value (fun j t p => G.totalColumn p j t) p ≠ 0}

/-- A finite-minor version of the analytic generic double-rank theorem.
The cell compatibility tests are actual finite derivative evaluations. -/
theorem generic_double_rank_minor {d : ℕ} (G : Family 2 d)
    (ho : IsOpen G.W) (hc : IsConnected G.W) (ha : G.IsAnalytic) :
    ∃ M : DoubleRankMinor G, M.point.size ≤ d ∧ M.curve.size ≤ d + 2 ∧
      IsOpen M.regularSet ∧ G.W ⊆ closure M.regularSet ∧
      ∀ p ∈ M.regularSet,
        G.pointRank p = M.point.size ∧ G.curveRank p = M.curve.size := by
  obtain ⟨Mp, hmp, _, hpO, hpD, _, hpEq⟩ :=
    generic_rank_evaluation_minor (fun j t p => G.uColumn p j t) G.W ho hc.nonempty
      hc.isPreconnected (G.uColumn_analytic ho ha)
  obtain ⟨Mc, hmc, _, hcO, hcD, _, hcEq⟩ :=
    generic_rank_evaluation_minor (fun j t p => G.totalColumn p j t) G.W ho hc.nonempty
      hc.isPreconnected (G.totalColumn_analytic ho ha)
  let M : DoubleRankMinor G := ⟨Mp, Mc⟩
  have hset : M.regularSet = {p | p ∈ G.W ∧ Mp.value (fun j t p => G.uColumn p j t) p ≠ 0} ∩
      {p | p ∈ G.W ∧ Mc.value (fun j t p => G.totalColumn p j t) p ≠ 0} := by
    ext p; simp [DoubleRankMinor.regularSet, M, and_assoc, and_left_comm, and_comm]
  refine ⟨M, hmp, hmc, hset ▸ hpO.inter hcO, ?_, ?_⟩
  · rw [hset]
    exact relative_dense_open_inter G.W _ _ ho hpO (fun _ hp => hp.1) hpD hcD
  · intro p hp
    refine ⟨hpEq p hp.1 hp.2.1, ?_⟩
    have he := hcEq p hp.1 hp.2.2
    change finrank ℝ (span ℝ (range (G.totalColumn p))) = Mc.size at he
    rw [G.totalColumn_span] at he
    exact he

end PlanarNikodym
