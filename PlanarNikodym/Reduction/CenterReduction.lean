import PlanarNikodym.Geometry.CenterCoordinates
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

noncomputable section
open Set Filter Submodule Module Metric
open scoped Topology
namespace PlanarNikodym

theorem zero_block_range {X : Type*} {b c : ℕ}
    (φ : X → BlockParameters 0 b c → ℝ) (p : BlockParameters 0 b c) :
    (functionDerivative φ p).range = (wDerivative φ p).range ⊔ (etaDerivative φ p).range := by
  apply le_antisymm
  · rintro g ⟨k, rfl⟩
    have hk : k.1.1 = 0 := Subsingleton.elim _ _
    have heq : k = wIn 0 b c k.1.2 + etaIn 0 b c k.2 := by
      ext <;> simp [wIn, etaIn, hk]
      exact Fin.elim0 ‹Fin 0›
    rw [heq, map_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨k.1.2, rfl⟩)
      (Submodule.mem_sup_right ⟨k.2, rfl⟩)
  · apply sup_le
    · rintro g ⟨w, rfl⟩
      exact ⟨wIn 0 b c w, rfl⟩
    · rintro g ⟨η, rfl⟩
      exact ⟨etaIn 0 b c η, rfl⟩

/-- Freeze the centre coordinate complementary to j at its basepoint value. -/
def centerSlice {d : ℕ} (j : Fin 2) (q p : Parameters 2 d) : Parameters 2 d :=
  ((fun i => if i = j then p.1 i else q.1 i), p.2)

theorem centerBlock_slice {d : ℕ} (j : Fin 2) (q p : Parameters 2 d) :
    centerBlockEquiv d j (((centerBlockEquiv d j).symm p).1,
      ((centerBlockEquiv d j).symm q).2) = centerSlice j q p := by
  apply Prod.ext
  · ext i
    fin_cases j <;> fin_cases i <;> simp [centerSlice]
  · rfl

/-- Corollary 6.3. j is the effective centre coordinate; j.rev is the
coordinate kept by the chart. Thus j=1 is the paper's displayed ordering,
and j=0 is its allowed interchange of the two centre coordinates. -/
theorem corollary_6_3 {d : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W) (ha : G.IsAnalytic)
    (hp : ∀ p ∈ G.W, G.pointRank p = d)
    (hc : ∀ p ∈ G.W, G.curveRank p = d + 1) (q : Parameters 2 d) (hq : q ∈ G.W) :
    ∃ j : Fin 2, ∃ E : OpenPartialHomeomorph (Parameters 2 d) (Parameters 2 d),
      q ∈ E.source ∧ E.source ⊆ G.W ∧ E.target ⊆ G.W ∧
      AnalyticOnNhd ℝ E E.source ∧ AnalyticOnNhd ℝ E.symm E.target ∧
      (∀ p, (E p).1 j.rev = p.1 j.rev) ∧
      (∀ p ∈ E.source, p.1 j.rev = q.1 j.rev → E p = p) ∧
      ∀ p ∈ E.source, ∀ t ∈ G.I.carrier, G.γ t (E p) = G.γ t (centerSlice j q p) := by
  obtain ⟨j, hj⟩ := G.exists_transverse_center q (hp q hq) (hc q hq)
  let H := centerBlockEquiv d j
  let q' := H.symm q
  let φ := fun (t : G.I.carrier) p => G.γ t (H p)
  have hHq : H q' = q := H.apply_symm_apply q
  have hφ : ∀ t, AnalyticAt ℝ (φ t) q' := by
    intro t
    have ht : AnalyticAt ℝ (G.γ t) (H q') := by
      rw [hHq]; exact G.parameter_analytic ha q hq t
    exact ht.comp (H.analyticAt q')
  have hi := center_wDerivative_injective G q
    (fun t => (G.parameter_analytic ha q hq t).differentiableAt) (hp q hq) j hj
  have hn := wDerivative_rank_near φ q' hφ hi
  have hpre : H ⁻¹' G.W ∈ 𝓝 q' :=
    (hW.preimage H.continuous).mem_nhds (by change H q' ∈ G.W; rwa [hHq])
  obtain ⟨S, hS, hSo, hqS⟩ := _root_.mem_nhds_iff.mp (inter_mem hpre hn)
  have hr : ∀ p ∈ S, BlockRank φ p := by
    intro p hps
    have hpW := (hS hps).1
    refine ⟨(hS hps).2, ?_⟩
    rw [← zero_block_range, functionDerivative_comp _ H p
      (fun t => (G.parameter_analytic ha _ hpW t).differentiableAt) H.differentiableAt, H.fderiv]
    change finrank ℝ ((functionDerivative (fun (t : G.I.carrier) => G.γ t) (H p)).comp H.toLinearMap).range = d + 1
    rw [range_comp_eq_of_surjective _ _ H.surjective,
      ← G.curveSpace_eq_range _ (fun t => (G.parameter_analytic ha _ hpW t).differentiableAt)]
    exact hc _ hpW
  obtain ⟨r, hrr, F, hsrc, hsrcS, htarS, _, hFa, hFia, hcoord, hnorm, hid⟩ :=
    lemma_6_1 φ S hSo q' hqS
      (fun t p hps => (G.parameter_analytic ha _ (hS hps).1 t).comp (H.analyticAt p)) hr
  let E := (H.symm.toHomeomorph.transOpenPartialHomeomorph F).transHomeomorph H.toHomeomorph
  have hE (p : Parameters 2 d) : E p = H (F (H.symm p)) := rfl
  have hEi (p : Parameters 2 d) : E.symm p = H (F.symm (H.symm p)) := rfl
  refine ⟨j, E, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change q' ∈ F.source
    rw [hsrc]
    exact mem_ball_self hrr
  · intro p hps
    change H.symm p ∈ F.source at hps
    have ht := (hS (hsrcS hps)).1
    change H (H.symm p) ∈ G.W at ht
    simpa only [H.apply_symm_apply] using ht
  · intro p hpt
    change H.symm p ∈ F.target at hpt
    have ht := (hS (htarS hpt)).1
    change H (H.symm p) ∈ G.W at ht
    simpa only [H.apply_symm_apply] using ht
  · intro p hps
    change H.symm p ∈ F.source at hps
    exact (H.analyticAt _).comp (f := fun s => F (H.symm s))
      ((hFa _ hps).comp (H.symm.analyticAt p))
  · intro p hpt
    change H.symm p ∈ F.target at hpt
    exact (H.analyticAt _).comp (f := fun s => F.symm (H.symm s))
      ((hFia _ hpt).comp (H.symm.analyticAt p))
  · intro p
    rw [hE, centerBlockEquiv_other, (hcoord _).2]
    rfl
  · intro p hps hη
    change H.symm p ∈ F.source at hps
    rw [hE, hnorm _ hps]
    · exact H.apply_symm_apply p
    · ext i
      fin_cases i
      exact hη
  · intro p hps t ht
    change H.symm p ∈ F.source at hps
    change φ ⟨t, ht⟩ (F (H.symm p)) = _
    rw [hid _ hps]
    exact congrArg (G.γ t) (centerBlock_slice j q p)

/-- Projection-valued interface exposing the two compensating functions
in the displayed statement of Corollary 6.3. -/
theorem corollary_6_3_functions {d : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W) (ha : G.IsAnalytic)
    (hp : ∀ p ∈ G.W, G.pointRank p = d)
    (hc : ∀ p ∈ G.W, G.curveRank p = d + 1) (q : Parameters 2 d) (hq : q ∈ G.W) :
    ∃ j : Fin 2, ∃ κz : Parameters 2 d → ℝ, ∃ κu : Parameters 2 d → Aux d,
    ∃ E : OpenPartialHomeomorph (Parameters 2 d) (Parameters 2 d),
      q ∈ E.source ∧ E.source ⊆ G.W ∧ E.target ⊆ G.W ∧
      AnalyticOnNhd ℝ κz E.source ∧ AnalyticOnNhd ℝ κu E.source ∧
      AnalyticOnNhd ℝ E E.source ∧ AnalyticOnNhd ℝ E.symm E.target ∧
      (∀ p, E p = ((fun i => if i = j then κz p else p.1 i), κu p)) ∧
      (∀ p ∈ E.source, p.1 j.rev = q.1 j.rev → κz p = p.1 j ∧ κu p = p.2) ∧
      ∀ p ∈ E.source, ∀ t ∈ G.I.carrier, G.γ t (E p) = G.γ t (centerSlice j q p) := by
  obtain ⟨j, E, hqs, hsW, htW, hea, heia, hcoord, hnorm, hid⟩ :=
    corollary_6_3 G hW ha hp hc q hq
  refine ⟨j, fun p => (E p).1 j, fun p => (E p).2, E,
    hqs, hsW, htW, ?_, ?_, hea, heia, ?_, ?_, hid⟩
  · intro p hps
    exact ((ContinuousLinearMap.proj j : Base 2 →L[ℝ] ℝ).analyticAt _).comp
      (analyticAt_fst.comp (hea p hps))
  · intro p hps
    exact analyticAt_snd.comp (hea p hps)
  · intro p
    apply Prod.ext
    · ext i
      by_cases hij : i = j
      · simp [hij]
      · have hi : i = j.rev := by fin_cases i <;> fin_cases j <;> simp_all
        change (E p).1 i = if i = j then (E p).1 j else p.1 i
        rw [if_neg hij, hi]
        exact hcoord p
    · rfl
  · intro p hps hη
    exact ⟨congrArg (fun x => x.1 j) (hnorm p hps hη),
      congrArg Prod.snd (hnorm p hps hη)⟩

end PlanarNikodym
