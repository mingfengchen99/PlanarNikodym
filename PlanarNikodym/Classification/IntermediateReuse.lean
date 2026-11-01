import PlanarNikodym.Classification.RankOneLocal
import PlanarNikodym.Core.Statements

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology
namespace PlanarNikodym

/-- Vary only the centre coordinate which Corollary 6.3 keeps fixed. -/
def centerLine {d : ℕ} (j : Fin 2) (q : Parameters 2 d) (s : ℝ) : Parameters 2 d :=
  ((fun i => if i = j.rev then s else q.1 i), q.2)

@[simp] theorem centerLine_base {d : ℕ} (j : Fin 2) (q : Parameters 2 d) :
    centerLine j q (q.1 j.rev) = q := by
  apply Prod.ext
  · ext i; by_cases hi : i = j.rev <;> simp [centerLine, hi]
  · rfl

@[simp] theorem centerLine_slice {d : ℕ} (j : Fin 2) (q : Parameters 2 d) (s : ℝ) :
    centerSlice j q (centerLine j q s) = q := by
  apply Prod.ext
  · ext i; fin_cases j <;> fin_cases i <;> simp [centerLine, centerSlice]
  · rfl

theorem centerLine_analytic {d : ℕ} (j : Fin 2) (q : Parameters 2 d) (s : ℝ) :
    AnalyticAt ℝ (centerLine j q) s := by
  apply AnalyticAt.prod _ analyticAt_const
  apply AnalyticAt.pi
  intro i
  change AnalyticAt ℝ (fun x : ℝ => if i = j.rev then x else q.1 i) s
  by_cases hi : i = j.rev
  · simp only [hi, if_true]
    exact analyticAt_id
  · simp only [hi, if_false]
    exact analyticAt_const

/-- Every curve in the full auxiliary-rank, intermediate curve-rank case is
locally reused. The centre arc has a Lipschitz left inverse, so its positive
H¹ measure is proved rather than assumed. This includes d=0. -/
theorem full_intermediate_locallyReused {d : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W) (ha : G.IsAnalytic)
    (hp : ∀ p ∈ G.W, G.pointRank p = d)
    (hc : ∀ p ∈ G.W, G.curveRank p = d + 1)
    (q : Parameters 2 d) (hq : q ∈ G.W) : G.LocallyReused q := by
  obtain ⟨j, E, hqs, _, htW, _, _, hkeep, hnorm, hid⟩ :=
    corollary_6_3 G hW ha hp hc q hq
  have hEq : E q = q := hnorm q hqs rfl
  refine ⟨hq, ?_⟩
  intro U hU
  let b := q.1 j.rev
  let l := centerLine j q
  let ψ : ℝ → Base 2 := fun s => (E (l s)).1
  let P : Base 2 → ℝ := fun z => z j.rev
  have hlq : l b = q := centerLine_base j q
  have hlc : Continuous l := continuous_iff_continuousAt.mpr
    (fun s => (centerLine_analytic j q s).continuousAt)
  have hec : ContinuousAt (fun s => E (l s)) b := by
    have hEc : ContinuousAt E (l b) := by rw [hlq]; exact E.continuousAt hqs
    exact hEc.comp hlc.continuousAt
  have hn : {s | l s ∈ E.source ∧ E (l s) ∈ U} ∈ 𝓝 b := by
    apply inter_mem
    · exact hlc.continuousAt.preimage_mem_nhds (hlq ▸ E.open_source.mem_nhds hqs)
    · exact hec.preimage_mem_nhds (by simpa only [hlq, hEq] using hU)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  let T := Icc (b - r / 2) (b + r / 2)
  have hT (s : ℝ) (hs : s ∈ T) : l s ∈ E.source ∧ E (l s) ∈ U := by
    apply hball
    rw [mem_ball, Real.dist_eq]
    apply lt_of_le_of_lt (abs_le.mpr ⟨?_, ?_⟩) (half_lt_self hr)
    · linarith [hs.1]
    · linarith [hs.2]
  have hcψ : ContinuousOn ψ T := continuous_fst.comp_continuousOn
    (E.continuousOn.comp hlc.continuousOn (fun s hs => (hT s hs).1))
  have hP : LipschitzWith _ P := (ContinuousLinearMap.proj j.rev : Base 2 →L[ℝ] ℝ).lipschitz
  have hleft : ∀ s ∈ T, P (ψ s) = s := by
    intro s _
    change (E (l s)).1 j.rev = s
    rw [hkeep]
    simp [l, centerLine]
  have hpos := positive_part_of_curve_left_inverse ψ P hP
    (by linarith : b - r / 2 < b + r / 2) hcψ hleft
  apply hpos.mono
  rintro z ⟨s, hs, rfl⟩
  refine ⟨E (l s), ⟨⟨htW (E.map_source (hT s hs).1), ?_⟩, (hT s hs).2⟩, rfl⟩
  apply (G.sameCurve_iff_curve_eq _ _).mp
  intro t ht
  simpa only [l, centerLine_slice] using hid (l s) (hT s hs).1 t ht

/-- Corollary 6.2 transfers the local reuse result back through all redundant
auxiliary parameters. No positive point rank or boundedness is needed here. -/
theorem intermediate_locallyReused {d m : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W) (ha : G.IsAnalytic) (hr : ConstantRanks G m (m + 1))
    (q : Parameters 2 d) (hq : q ∈ G.W) : G.LocallyReused q := by
  refine ⟨hq, ?_⟩
  intro U hU
  obtain ⟨V, hV, hVo, hqV⟩ := _root_.mem_nhds_iff.mp (inter_mem hU (hW.mem_nhds hq))
  let G₀ := G.restrictTo V
  have hVW : V ⊆ G.W := fun p hp => (hV hp).2
  obtain ⟨L, _, hqL, hLV, Wz, Wu, H, hzO, huO, _, _, _, hprod, hHa, hHr, he⟩ :=
    corollary_6_2 G₀ hVo (ha.restrictTo hVW) (fun p hp => (hr p (hVW hp)).1)
      (fun p hp => (hr p (hVW hp)).2) q hqV
  obtain ⟨u, hu, hcurve⟩ := (he q.1) ▸ (show G₀.curve q ∈ G₀.curvesAtOn L q.1 from
    ⟨q.2, hqL, rfl⟩)
  have hre := full_intermediate_locallyReused H (hprod ▸ hzO.prod huO) hHa
    (fun p hp => (hHr p hp).1) (fun p hp => (hHr p hp).2) (q.1, u) hu
  have hpos : HasPositivePart (Measure.hausdorffMeasure 1) (H.centersOf (H.curve (q.1, u))) := by
    have hh := hre.2 univ (by simp)
    simpa only [Family.centersOf, inter_univ] using hh
  apply hpos.mono
  intro z hz
  have hz' : H.curve (q.1, u) ∈ H.curvesAtOn H.W z := (H.mem_centersOf _ z).mp hz
  obtain ⟨v, hv, hvc⟩ := (he z).symm ▸ hz'
  exact ⟨(z, v), ⟨⟨hVW (hLV hv), hvc.trans hcurve⟩, (hV (hLV hv)).1⟩, rfl⟩

theorem intermediate_hasLocalCurveReuse {d m : ℕ} (G : Family 2 d)
    (hWne : G.W.Nonempty) (hW : IsOpen G.W) (ha : G.IsAnalytic)
    (hr : ConstantRanks G m (m + 1)) : G.HasLocalCurveReuse :=
  G.hasLocalCurveReuse_of_all hW hWne (intermediate_locallyReused G hW ha hr)

end PlanarNikodym
