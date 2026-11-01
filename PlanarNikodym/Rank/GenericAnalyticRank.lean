import PlanarNikodym.Rank.AnalyticCoefficients
import PlanarNikodym.Geometry.AnalyticZeros
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

noncomputable section
open Set Filter Submodule Module
open scoped Topology
namespace PlanarNikodym

/-- Select a basis from a finite generating family, retaining the indices. -/
theorem select_independent_generators {V : Type*} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (v : Fin n → V) :
    ∃ σ : Fin (finrank ℝ (span ℝ (range v))) → Fin n,
      LinearIndependent ℝ (fun j => v (σ j)) := by
  classical
  let hs₀ := linearIndepOn_empty ℝ v
  let s : Set (Fin n) := hs₀.extend (empty_subset univ)
  have hs : LinearIndepOn ℝ v s := hs₀.linearIndepOn_extend (empty_subset univ)
  have hspan : span ℝ (range (fun j : s => v j)) = span ℝ (range v) := by
    rw [← Set.image_eq_range v s]
    simpa only [Set.image_univ] using hs₀.span_image_extend_eq_span_image (empty_subset univ)
  have hcard : Fintype.card s = finrank ℝ (span ℝ (range v)) := by
    rw [← hspan, finrank_span_eq_card hs]
  let e : Fin (finrank ℝ (span ℝ (range v))) ≃ s :=
    Fintype.equivOfCardEq (by simp [hcard])
  exact ⟨fun j => e j, hs.comp e e.injective⟩

/-- The nonzero locus of a nontrivial analytic scalar function on a
connected open set is open and relatively dense. No definability input. -/
theorem analytic_nonzero_locus {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : Set E) (hW : IsOpen W) (hconn : IsPreconnected W)
    (F : E → ℝ) (ha : AnalyticOnNhd ℝ F W) (q : E) (hq : q ∈ W) (hFq : F q ≠ 0) :
    IsOpen {x | x ∈ W ∧ F x ≠ 0} ∧ W ⊆ closure {x | x ∈ W ∧ F x ≠ 0} := by
  let D := {x | x ∈ W ∧ F x ≠ 0}
  have hD : IsOpen D := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    exact inter_mem (hW.mem_nhds hx.1)
      ((ha x hx.1).continuousAt.eventually_ne hx.2)
  refine ⟨hD, ?_⟩
  intro x hx
  by_contra hn
  have hV : W ∩ (closure D)ᶜ ∈ 𝓝 x :=
    inter_mem (hW.mem_nhds hx) (isClosed_closure.isOpen_compl.mem_nhds hn)
  have hz : F =ᶠ[𝓝 x] 0 := by
    filter_upwards [hV] with y hy
    by_contra hny
    exact hy.2 (subset_closure ⟨hy.1, hny⟩)
  have he := ha.eqOn_of_preconnected_of_eventuallyEq (fun _ _ => analyticAt_const)
    hconn hx hz
  exact hFq (he hq)

/-- The analytic part of Corollary 5.4. A maximal-rank finite family has
constant rank on an open relatively dense set; its complement is contained
in the zero set of one explicitly constructed nontrivial analytic minor.
Dimension, definability and cell decomposition are separate obligations. -/
theorem generic_analytic_function_rank {E X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (f : Fin n → X → E → ℝ) (W : Set E) (hW : IsOpen W)
    (hne : W.Nonempty) (hconn : IsPreconnected W)
    (hf : ∀ j t, AnalyticOnNhd ℝ (f j t) W) :
    ∃ m : ℕ, m ≤ n ∧ ∃ F : E → ℝ, AnalyticOnNhd ℝ F W ∧
      (∃ q ∈ W, F q ≠ 0) ∧ IsOpen {x | x ∈ W ∧ F x ≠ 0} ∧
      W ⊆ closure {x | x ∈ W ∧ F x ≠ 0} ∧
      (∀ x ∈ W, finrank ℝ (span ℝ (range (fun j t => f j t x))) ≤ m) ∧
      ∀ x ∈ W, F x ≠ 0 → finrank ℝ (span ℝ (range (fun j t => f j t x))) = m := by
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
  let F : E → ℝ := fun x => Matrix.det (fun i j => f (σ j) (t i) x)
  have hFa : AnalyticOnNhd ℝ F W := fun x hx => analyticAt_det (fun i j => hf (σ j) (t i) x hx)
  have hFq : F q ≠ 0 := ht
  obtain ⟨hDo, hDd⟩ := analytic_nonzero_locus W hW hconn F hFa q hq hFq
  refine ⟨r q, hr q, F, hFa, ⟨q, hq, hFq⟩, hDo, hDd, ?_, ?_⟩
  · intro x hx
    exact hmax (r x) (mem_image_of_mem r hx)
  · intro x hx hFx
    apply le_antisymm (hmax (r x) (mem_image_of_mem r hx))
    have hli := independent_of_eval_det_ne_zero (fun j s => f (σ j) s x) t hFx
    have hle : span ℝ (range (fun j s => f (σ j) s x)) ≤
        span ℝ (range (fun j s => f j s x)) := span_mono (by
      rintro _ ⟨j, rfl⟩; exact mem_range_self (σ j))
    haveI := FiniteDimensional.span_of_finite ℝ (finite_range (fun j s => f j s x))
    have hdim := Submodule.finrank_mono hle
    rw [finrank_span_eq_card hli, Fintype.card_fin] at hdim
    exact hdim

/-- The analytic zero-set alternative in Corollary 5.4, for any rank
threshold. The o-minimal dimension assertion is not part of this theorem. -/
theorem rank_drop_analytic_dichotomy {E X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (f : Fin n → X → E → ℝ) (W : Set E) (hW : IsOpen W)
    (hne : W.Nonempty) (hconn : IsPreconnected W)
    (hf : ∀ j t, AnalyticOnNhd ℝ (f j t) W) (k : ℕ) :
    (∀ x ∈ W, finrank ℝ (span ℝ (range (fun j t => f j t x))) ≤ k) ∨
      ∃ F : E → ℝ, AnalyticOnNhd ℝ F W ∧ (∃ q ∈ W, F q ≠ 0) ∧
        {x | x ∈ W ∧ finrank ℝ (span ℝ (range (fun j t => f j t x))) ≤ k} ⊆
          {x | x ∈ W ∧ F x = 0} := by
  obtain ⟨m, _, F, hF, hFn, _, _, hmax, heq⟩ :=
    generic_analytic_function_rank f W hW hne hconn hf
  by_cases hmk : m ≤ k
  · exact Or.inl (fun x hx => (hmax x hx).trans hmk)
  · refine Or.inr ⟨F, hF, hFn, ?_⟩
    intro x hx
    refine ⟨hx.1, ?_⟩
    by_contra hn
    have he := heq x hx.1 hn
    exact hmk (he ▸ hx.2)

end PlanarNikodym
