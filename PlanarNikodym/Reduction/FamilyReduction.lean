import PlanarNikodym.Geometry.BlockGeometry

noncomputable section
open Set Filter Submodule Module Metric
open scoped Topology
namespace PlanarNikodym

def Family.curvesAtOn {d : ℕ} (G : Family 2 d) (U : Set (Parameters 2 d))
    (z : Base 2) : Set (Set Plane) :=
  {β | ∃ u, (z, u) ∈ U ∧ G.curve (z, u) = β}

theorem Family.parameter_analytic {n d : ℕ} (G : Family n d) (ha : G.IsAnalytic)
    (p : Parameters n d) (hp : p ∈ G.W) (t : G.I.carrier) :
    AnalyticAt ℝ (G.γ t) p :=
  (ha (t, p) ⟨t.property, hp⟩).comp (analyticAt_const.prod analyticAt_id)

/-- The auxiliary splitting and the neighbourhood on which the hypotheses
of Lemma 6.1 hold. The splitting is selected from the actual derivatives. -/
theorem Family.exists_rank_block {d m : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W) (ha : G.IsAnalytic)
    (hr : ∀ p ∈ G.W, G.pointRank p = m) (q : Parameters 2 d) (hq : q ∈ G.W) :
    ∃ e : (Aux m × Aux (d - m)) ≃L[ℝ] Aux d,
    ∃ S : Set (BlockParameters 2 m (d - m)), IsOpen S ∧
      (blockCoordinateEquiv e).symm q ∈ S ∧
      S ⊆ blockCoordinateEquiv e ⁻¹' G.W ∧
      ∀ p ∈ S, BlockRank (fun (t : G.I.carrier) s => G.γ t (blockCoordinateEquiv e s)) p := by
  let L := functionDerivative (fun (t : G.I.carrier) u => G.γ t (q.1, u)) q.2
  have hL : finrank ℝ L.range = m := by
    rw [← G.pointSpace_eq_range]
    exact hr q hq
  obtain ⟨e, he⟩ := exists_effective_split L hL
  let H := blockCoordinateEquiv (a := 2) e
  let q' := H.symm q
  let φ := fun (t : G.I.carrier) p => G.γ t (H p)
  have hHq : H q' = q := H.apply_symm_apply q
  have hφ : ∀ t, AnalyticAt ℝ (φ t) q' := by
    intro t
    have ht : AnalyticAt ℝ (G.γ t) (H q') := by
      rw [hHq]
      exact G.parameter_analytic ha q hq t
    exact ht.comp (f := fun p => H p) (H.analyticAt q')
  have hw : Function.Injective (wDerivative φ q') := by
    rw [wDerivative_coordinates _ e q' (fun t => by
      rw [hHq]; exact (G.parameter_analytic ha q hq t).differentiableAt)]
    have hq₁ : q'.1.1 = q.1 := congrArg Prod.fst hHq
    have hq₂ : e (q'.1.2, q'.2) = q.2 := congrArg Prod.snd hHq
    rw [hq₁, hq₂]
    exact he
  have hn := wDerivative_rank_near φ q' hφ hw
  have hpre : H ⁻¹' G.W ∈ 𝓝 q' :=
    (hW.preimage H.continuous).mem_nhds (by change H q' ∈ G.W; rwa [hHq])
  obtain ⟨S, hS, hSo, hqS⟩ := _root_.mem_nhds_iff.mp (inter_mem hpre hn)
  refine ⟨e, S, hSo, hqS, fun p hp => (hS hp).1, ?_⟩
  intro p hp
  have hpW := (hS hp).1
  refine ⟨(hS hp).2, ?_⟩
  rw [vertical_range_coordinates _ e p (fun t => (G.parameter_analytic ha _ hpW t).differentiableAt)]
  change finrank ℝ (functionDerivative (fun (t : G.I.carrier) u =>
    G.γ t ((H p).1, u)) (H p).2).range = m
  rw [← G.pointSpace_eq_range (H p)]
  exact hr _ hpW

/-- Corollary 6.2: local elimination of all unused auxiliary variables.
The equality of families is stated separately for every centre. -/
theorem corollary_6_2 {d m k : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W) (ha : G.IsAnalytic)
    (hp : ∀ p ∈ G.W, G.pointRank p = m)
    (hc : ∀ p ∈ G.W, G.curveRank p = k) (q : Parameters 2 d) (hq : q ∈ G.W) :
    ∃ W₁ : Set (Parameters 2 d), IsOpen W₁ ∧ q ∈ W₁ ∧ W₁ ⊆ G.W ∧
    ∃ Wz : Set (Base 2), ∃ Wu : Set (Aux m), ∃ G' : Family 2 m,
      IsOpen Wz ∧ IsOpen Wu ∧ q.1 ∈ Wz ∧ Wu.Nonempty ∧
      G'.I = G.I ∧ G'.W = Wz ×ˢ Wu ∧ G'.IsAnalytic ∧
      (∀ p ∈ G'.W, G'.pointRank p = m ∧ G'.curveRank p = k) ∧
      ∀ z, G.curvesAtOn W₁ z = G'.curvesAtOn G'.W z := by
  obtain ⟨e, S, hSo, hqS, hSW, hr⟩ := G.exists_rank_block hW ha hp q hq
  let H := blockCoordinateEquiv (a := 2) e
  let q' := H.symm q
  let φ := fun (t : G.I.carrier) p => G.γ t (H p)
  have hHq : H q' = q := H.apply_symm_apply q
  have hφ : ∀ t, AnalyticOnNhd ℝ (φ t) S := by
    intro t p hps
    exact (G.parameter_analytic ha _ (hSW hps) t).comp (H.analyticAt p)
  obtain ⟨r, hrr, F, hsrc, hsrcS, htarS, hFq, hFa, hFia, hcoord, hnorm, hid⟩ :=
    lemma_6_1 φ S hSo q' hqS hφ hr
  let W₁ := H '' F.target
  let G' : Family 2 m :=
    ⟨G.I, ball q'.1.1 r ×ˢ ball q'.1.2 r,
      fun t p => G.γ t (H (p, q'.2))⟩
  have hbase (p : Parameters 2 m) (hpm : p ∈ G'.W) : (p, q'.2) ∈ F.source := by
    rw [hsrc, ← ball_prod_same, ← ball_prod_same]
    exact ⟨hpm, mem_ball_self hrr⟩
  have hbaseW (p : Parameters 2 m) (hpm : p ∈ G'.W) : H (p, q'.2) ∈ G.W :=
    hSW (hsrcS (hbase p hpm))
  have hbaseA (p : Parameters 2 m) (hpm : p ∈ G'.W) (t : G.I.carrier) :
      AnalyticAt ℝ (φ t) (p, q'.2) := hφ t _ (hsrcS (hbase p hpm))
  refine ⟨W₁, H.toHomeomorph.isOpenMap _ F.open_target, ?_, ?_,
    ball q'.1.1 r, ball q'.1.2 r, G', isOpen_ball, isOpen_ball, ?_,
    ⟨q'.1.2, mem_ball_self hrr⟩, rfl, rfl, ?_, ?_, ?_⟩
  · refine ⟨q', ?_, hHq⟩
    rw [← hFq]
    apply F.map_source
    rw [hsrc]
    exact mem_ball_self hrr
  · rintro p ⟨x, hx, rfl⟩
    exact hSW (htarS hx)
  · have hz := congrArg Prod.fst hHq
    change q.1 ∈ ball q'.1.1 r
    rw [← hz]
    exact mem_ball_self hrr
  · intro tp htp
    let ins : ℝ × Parameters 2 m → ℝ × Parameters 2 d := fun x => (x.1, H (x.2, q'.2))
    have hai : AnalyticAt ℝ ins tp :=
      analyticAt_fst.prod ((H.analyticAt _).comp
        (f := fun x : ℝ × Parameters 2 m => (x.2, q'.2))
        (analyticAt_snd.prod analyticAt_const))
    exact (ha (ins tp) ⟨htp.1, hbaseW tp.2 htp.2⟩).comp hai
  · intro p hpm
    have hf := fun t => (hbaseA p hpm t).differentiableAt
    have hg : ∀ t : G.I.carrier, DifferentiableAt ℝ (G'.γ t) p := by
      intro t
      exact ((hbaseA p hpm t).comp (f := fun v : Parameters 2 m => (v, q'.2))
        (analyticAt_id.prod analyticAt_const)).differentiableAt
    constructor
    · change finrank ℝ (G'.pointSpace p) = m
      rw [G'.pointSpace_eq_range]
      change finrank ℝ (functionDerivative (fun (t : G.I.carrier) w =>
        φ t ((p.1, w), q'.2)) p.2).range = m
      rw [← wDerivative_eq_slice φ (p, q'.2) hf]
      exact (hr _ (hsrcS (hbase p hpm))).1
    · change finrank ℝ (G'.curveSpace p) = k
      rw [G'.curveSpace_eq_range p hg]
      have hs := restrict_eta_range φ (p, q'.2) hf (hr _ (hsrcS (hbase p hpm)))
      change finrank ℝ (functionDerivative (fun (t : G.I.carrier) v => φ t (v, q'.2)) p).range = k
      rw [← hs, functionDerivative_comp _ H _
        (fun t => (G.parameter_analytic ha _ (hbaseW p hpm) t).differentiableAt) H.differentiableAt,
        H.fderiv]
      change finrank ℝ ((functionDerivative (fun (t : G.I.carrier) => G.γ t)
        (H (p, q'.2))).comp H.toLinearMap).range = k
      rw [range_comp_eq_of_surjective _ _ H.surjective]
      rw [← G.curveSpace_eq_range _
        (fun t => (G.parameter_analytic ha _ (hbaseW p hpm) t).differentiableAt)]
      exact hc _ (hbaseW p hpm)
  · intro z
    ext β
    constructor
    · rintro ⟨u, ⟨y, hy, hye⟩, hcurve⟩
      let x := F.symm y
      have hx : x ∈ F.source := F.map_target hy
      have hxy : F x = y := F.right_inv hy
      have hz : x.1.1 = z := by
        have h := congrArg Prod.fst hye
        change y.1.1 = z at h
        rw [← hxy, (hcoord x).1] at h
        exact h
      have hxm : x.1 ∈ G'.W := by
        rw [hsrc, ← ball_prod_same, ← ball_prod_same] at hx
        exact hx.1
      refine ⟨x.1.2, hz ▸ hxm, ?_⟩
      have heq : G'.curve x.1 = G.curve (z, u) := by
        apply Set.image_congr
        intro t ht
        change (t, G'.γ t x.1) = (t, G.γ t (z, u))
        congr 1
        change φ ⟨t, ht⟩ (x.1, q'.2) = G.γ t (z, u)
        rw [← hid x hx ⟨t, ht⟩, hxy]
        exact congrArg (G.γ t) hye
      rw [← hz]
      exact heq.trans hcurve
    · rintro ⟨w, hw, hcurve⟩
      let x : BlockParameters 2 m (d - m) := ((z, w), q'.2)
      have hx : x ∈ F.source := hbase _ hw
      have hfx : F x = x := hnorm x hx rfl
      refine ⟨e (w, q'.2), ?_, ?_⟩
      · exact ⟨x, hfx ▸ F.map_source hx, rfl⟩
      · exact hcurve

end PlanarNikodym
