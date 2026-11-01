import PlanarNikodym.Rank.FiniteRankMinors
import PlanarNikodym.Cells.SemianalyticMissingBoundaryHausdorff

/-! Actual ambient evaluation minors on a connected parametrized stratum.
Density is proved on the source and pushed through the continuous chart;
the ambient minor remains analytic on the entire supplied closed window. -/
noncomputable section
open Set Filter Submodule Module
open scoped Topology
namespace PlanarNikodym

theorem AnalyticStratificationChart.generic_ambient_evaluation_minor
    {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (Q : AnalyticStratificationChart E) (K : Set E) (hQK : Q.image ⊆ K)
    (f : Fin n → X → E → ℝ) (hf : ∀ j t, AnalyticOnNhd ℝ (f j t) K) :
    ∃ M : EvaluationMinor n X, M.size ≤ n ∧ AnalyticOnNhd ℝ (M.value f) K ∧
      (∃ x ∈ Q.image, M.value f x ≠ 0) ∧
      Q.image ⊆ closure {x | x ∈ Q.image ∧ M.value f x ≠ 0} ∧
      (∀ x ∈ Q.image, finrank ℝ (span ℝ (range (fun j t => f j t x))) ≤ M.size) ∧
      ∀ x ∈ Q.image, M.value f x ≠ 0 →
        finrank ℝ (span ℝ (range (fun j t => f j t x))) = M.size := by
  obtain ⟨M, hm, hne, _, hdense, hmax, heq⟩ := generic_rank_evaluation_minor
    (fun j t q => f j t (Q.map q)) Q.source Q.open_source Q.connected_source.nonempty
    Q.connected_source.isPreconnected (fun j t q hq =>
      (hf j t _ (hQK (mem_image_of_mem _ hq))).comp (Q.analytic_map q hq))
  refine ⟨M, hm, M.analytic f K hf, ?_, ?_, ?_, ?_⟩
  · obtain ⟨q, hq, hMq⟩ := hne
    exact ⟨Q.map q, mem_image_of_mem _ hq, hMq⟩
  · rintro _ ⟨q, hq, rfl⟩
    apply _root_.mem_closure_iff.mpr
    intro O hO hqO
    have hnear := (Q.analytic_map q hq).continuousAt.preimage_mem_nhds (hO.mem_nhds hqO)
    obtain ⟨V, hVsub, hV, hqV⟩ := mem_nhds_iff.mp hnear
    obtain ⟨r, hrV, hr⟩ := _root_.mem_closure_iff.mp (hdense hq) V hV hqV
    exact ⟨Q.map r, hVsub hrV, mem_image_of_mem _ hr.1, hr.2⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact hmax q hq
  · rintro _ ⟨q, hq, rfl⟩ hMq
    exact heq q hq hMq

theorem LocallySemianalytic.inter_analytic_nonzero
    {n : ℕ} {S : Set (Fin n → ℝ)} (hS : LocallySemianalytic S)
    (f : (Fin n → ℝ) → ℝ) (hf : AnalyticOnNhd ℝ f (closure S)) :
    LocallySemianalytic {x | x ∈ S ∧ f x ≠ 0} := by
  intro x
  by_cases hx : x ∈ closure S
  · have hsg := semianalyticAt_of_analytic_sign_germs (fun _ : Unit => f)
      (fun _ => hf x hx) (fun s => s () ≠ 1)
    have hsg' : SemianalyticAt {y | f y ≠ 0} x := by
      simpa only [ne_eq, oneDimensionalSign_eq_one] using hsg
    exact SemianalyticAt.inter (hS x) hsg'
  · have hempty : SemianalyticAt (∅ : Set (Fin n → ℝ)) x :=
      ⟨univ, isOpen_univ, mem_univ _, Empty, inferInstance, Empty.elim,
        (fun j => Empty.elim j), (fun _ => False), fun _ _ => Iff.rfl⟩
    apply hempty.congr
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
    simp only [mem_empty_iff_false, false_iff, not_and]
    exact fun hyS => (hy (subset_closure hyS)).elim

end PlanarNikodym
