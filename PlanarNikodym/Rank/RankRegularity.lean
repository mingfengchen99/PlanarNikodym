import PlanarNikodym.Rank.GenericAnalyticRank
import PlanarNikodym.Reduction.FamilyReduction

noncomputable section
open Set Filter Submodule Module
open scoped Topology
namespace PlanarNikodym

theorem Family.uColumn_analytic {d : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W) (ha : G.IsAnalytic) (j : Fin d) (t : G.I.carrier) :
    AnalyticOnNhd ℝ (fun p => G.uColumn p j t) G.W := by
  intro p hp
  have hK : AnalyticAt ℝ
      (fun q => fderiv ℝ (G.γ t) q (0, Pi.single j 1)) p :=
    ((ContinuousLinearMap.apply ℝ ℝ ((0, Pi.single j 1) : Parameters 2 d)).analyticAt _).comp
      (G.parameter_analytic ha p hp t).fderiv
  apply hK.congr
  filter_upwards [hW.mem_nhds hp] with q hq
  exact (congrArg (fun L : Aux d →L[ℝ] ℝ => L (Pi.single j 1))
    (fderiv_snd_slice (G.γ t) q (G.parameter_analytic ha q hq t).differentiableAt)).symm

theorem Family.zColumn_analytic {d : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W) (ha : G.IsAnalytic) (j : Fin 2) (t : G.I.carrier) :
    AnalyticOnNhd ℝ (fun p => G.zColumn p j t) G.W := by
  intro p hp
  have hK : AnalyticAt ℝ
      (fun q => fderiv ℝ (G.γ t) q (Pi.single j 1, 0)) p :=
    ((ContinuousLinearMap.apply ℝ ℝ ((Pi.single j 1, 0) : Parameters 2 d)).analyticAt _).comp
      (G.parameter_analytic ha p hp t).fderiv
  apply hK.congr
  filter_upwards [hW.mem_nhds hp] with q hq
  exact (congrArg (fun L : Base 2 →L[ℝ] ℝ => L (Pi.single j 1))
    (fderiv_fst_slice (G.γ t) q (G.parameter_analytic ha q hq t).differentiableAt)).symm

def Family.totalColumn {d : ℕ} (G : Family 2 d) (p : Parameters 2 d) :
    Fin (d + 2) → G.I.carrier → ℝ := Fin.append (G.uColumn p) (G.zColumn p)

theorem Family.totalColumn_analytic {d : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W) (ha : G.IsAnalytic) (j : Fin (d + 2)) (t : G.I.carrier) :
    AnalyticOnNhd ℝ (fun p => G.totalColumn p j t) G.W := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simpa [totalColumn] using G.uColumn_analytic hW ha j t
  · simpa [totalColumn] using G.zColumn_analytic hW ha j t

theorem Family.totalColumn_span {d : ℕ} (G : Family 2 d) (p : Parameters 2 d) :
    span ℝ (range (G.totalColumn p)) = G.curveSpace p := by
  have he : range (G.totalColumn p) = range (G.uColumn p) ∪ range (G.zColumn p) := by
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · exact Or.inl ⟨i, by simp [totalColumn]⟩
      · exact Or.inr ⟨i, by simp [totalColumn]⟩
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨i.castAdd 2, by simp [totalColumn]⟩
      · exact ⟨i.natAdd d, by simp [totalColumn]⟩
  rw [he, span_union]
  rfl

theorem relative_dense_open_inter {E : Type*} [TopologicalSpace E]
    (W D S : Set E) (hW : IsOpen W) (hD : IsOpen D) (hDW : D ⊆ W)
    (hDd : W ⊆ closure D) (hSd : W ⊆ closure S) : W ⊆ closure (D ∩ S) := by
  intro x hx
  apply _root_.mem_closure_iff.mpr
  intro O hO hxO
  obtain ⟨y, ⟨hyO, hyW⟩, hyD⟩ :=
    _root_.mem_closure_iff.mp (hDd hx) (O ∩ W) (hO.inter hW) ⟨hxO, hx⟩
  obtain ⟨z, ⟨hzO, hzD⟩, hzS⟩ :=
    _root_.mem_closure_iff.mp (hSd (hDW hyD)) (O ∩ D) (hO.inter hD) ⟨hyO, hyD⟩
  exact ⟨z, hzO, hzD, hzS⟩

/-- Analytic generic constant double rank (the analytic core of Corollary
5.5). The exceptional set is a union of two explicit analytic zero sets.
No o-minimal dimension or finite cell decomposition is asserted. -/
theorem generic_double_rank {d : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W) (hne : G.W.Nonempty) (hconn : IsPreconnected G.W)
    (ha : G.IsAnalytic) :
    ∃ mp mc : ℕ, mp ≤ d ∧ mc ≤ d + 2 ∧
      ∃ Fp Fc : Parameters 2 d → ℝ,
        AnalyticOnNhd ℝ Fp G.W ∧ AnalyticOnNhd ℝ Fc G.W ∧
        (∃ q ∈ G.W, Fp q ≠ 0) ∧ (∃ q ∈ G.W, Fc q ≠ 0) ∧
        ∃ D : Set (Parameters 2 d), IsOpen D ∧ D ⊆ G.W ∧ G.W ⊆ closure D ∧
          D = {p | p ∈ G.W ∧ Fp p ≠ 0 ∧ Fc p ≠ 0} ∧
          (∀ p ∈ G.W, G.pointRank p ≤ mp ∧ G.curveRank p ≤ mc) ∧
          ∀ p ∈ D, G.pointRank p = mp ∧ G.curveRank p = mc := by
  obtain ⟨mp, hmp, Fp, hFp, hpne, hpO, hpD, hpmax, hpEq⟩ :=
    generic_analytic_function_rank (fun j t p => G.uColumn p j t) G.W hW hne hconn
      (G.uColumn_analytic hW ha)
  obtain ⟨mc, hmc, Fc, hFc, hcne, hcO, hcD, hcmax, hcEq⟩ :=
    generic_analytic_function_rank (fun j t p => G.totalColumn p j t) G.W hW hne hconn
      (G.totalColumn_analytic hW ha)
  let D := {p | p ∈ G.W ∧ Fp p ≠ 0} ∩ {p | p ∈ G.W ∧ Fc p ≠ 0}
  refine ⟨mp, mc, hmp, hmc, Fp, Fc, hFp, hFc, hpne, hcne, D, hpO.inter hcO,
    fun p hp => hp.1.1, ?_, ?_, ?_, ?_⟩
  · exact relative_dense_open_inter G.W _ _ hW hpO (fun _ hp => hp.1) hpD hcD
  · ext p; simp [D, and_assoc, and_left_comm, and_comm]
  · intro p hp
    refine ⟨hpmax p hp, ?_⟩
    have hc := hcmax p hp
    change finrank ℝ (span ℝ (range (G.totalColumn p))) ≤ mc at hc
    rw [G.totalColumn_span] at hc
    exact hc
  · intro p hp
    refine ⟨hpEq p hp.1.1 hp.1.2, ?_⟩
    have hc := hcEq p hp.2.1 hp.2.2
    change finrank ℝ (span ℝ (range (G.totalColumn p))) = mc at hc
    rw [G.totalColumn_span] at hc
    exact hc

end PlanarNikodym
