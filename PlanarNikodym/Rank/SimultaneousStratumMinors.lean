import PlanarNikodym.Rank.StratumGenericMinor

noncomputable section
open Set Filter Submodule Module
open scoped Topology BigOperators
namespace PlanarNikodym

theorem AnalyticStratificationChart.simultaneous_ambient_minors
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (Q : AnalyticStratificationChart E) (K : Set E) (hQK : Q.image ⊆ K)
    (X : Fin 3 → Type) (f : (i : Fin 3) → Fin n → X i → E → ℝ)
    (hf : ∀ i j t, AnalyticOnNhd ℝ (f i j t) K) :
    ∃ h : E → ℝ, AnalyticOnNhd ℝ h K ∧
      Q.image ⊆ closure {x | x ∈ Q.image ∧ h x ≠ 0} ∧
      ∃ r : Fin 3 → ℕ, ∀ x ∈ Q.image, h x ≠ 0 →
        ∀ i, finrank ℝ (span ℝ (range (fun j t => f i j t x))) = r i := by
  classical
  have hminor (i : Fin 3) := generic_rank_evaluation_minor
    (fun j t q => f i j t (Q.map q)) Q.source Q.open_source Q.connected_source.nonempty
    Q.connected_source.isPreconnected (fun j t q hq =>
      (hf i j t _ (hQK (mem_image_of_mem _ hq))).comp (Q.analytic_map q hq))
  choose M hm hne hDo hDd hmax heq using hminor
  let h : E → ℝ := fun x => ∏ i : Fin 3, (M i).value (f i) x
  let D (i : Fin 3) := {q | q ∈ Q.source ∧ (M i).value (f i) (Q.map q) ≠ 0}
  have hDs (i : Fin 3) : D i ⊆ Q.source := fun _ hx => hx.1
  have hd01 := relative_dense_open_inter Q.source (D 0) (D 1) Q.open_source
    (hDo 0) (hDs 0) (hDd 0) (hDd 1)
  have hd012 := relative_dense_open_inter Q.source (D 0 ∩ D 1) (D 2) Q.open_source
    ((hDo 0).inter (hDo 1)) (fun _ hx => hx.1.1) hd01 (hDd 2)
  have hDn {q} (hq : q ∈ (D 0 ∩ D 1) ∩ D 2) : h (Q.map q) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    fin_cases i
    · exact hq.1.1.2
    · exact hq.1.2.2
    · exact hq.2.2
  refine ⟨h, fun x hx => Finset.analyticAt_fun_prod _ (fun i _ => (M i).analytic (f i) K (hf i) x hx),
    ?_, (fun i => (M i).size), ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    apply _root_.mem_closure_iff.mpr
    intro O hO hqO
    obtain ⟨V, hVsub, hV, hqV⟩ := mem_nhds_iff.mp
      ((Q.analytic_map q hq).continuousAt.preimage_mem_nhds (hO.mem_nhds hqO))
    obtain ⟨v, hvV, hv⟩ := _root_.mem_closure_iff.mp (hd012 hq) V hV hqV
    exact ⟨Q.map v, hVsub hvV, mem_image_of_mem _ hv.1.1.1, hDn hv⟩
  · rintro _ ⟨q, hq, rfl⟩ hh i
    have hMi : (M i).value (f i) (Q.map q) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hh) i (Finset.mem_univ _)
    exact heq i q hq hMi

end PlanarNikodym
