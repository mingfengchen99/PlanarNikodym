import PlanarNikodym.Core.ReuseBasics
import PlanarNikodym.Reduction.CenterReduction
import PlanarNikodym.Core.Statements

noncomputable section
open Set Filter Submodule Module Metric MeasureTheory
open scoped Topology
namespace PlanarNikodym

def auxCenterEquiv (d : ℕ) : BlockParameters 0 d 2 ≃L[ℝ] Parameters 2 d :=
  (show BlockParameters 0 d 2 ≃ₗ[ℝ] Parameters 2 d from
    { toFun := fun p => (p.2, p.1.2)
      invFun := fun p => ((0, p.2), p.1)
      left_inv := by
        intro p
        apply Prod.ext
        · exact Prod.ext (Subsingleton.elim _ _) rfl
        · rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toContinuousLinearEquiv

@[simp] theorem auxCenterEquiv_apply {d : ℕ} (p : BlockParameters 0 d 2) :
    auxCenterEquiv d p = (p.2, p.1.2) := rfl

theorem full_equal_ranks_massive {d : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W) (ha : G.IsAnalytic)
    (hp : ∀ p ∈ G.W, G.pointRank p = d) (hc : ∀ p ∈ G.W, G.curveRank p = d)
    (q : Parameters 2 d) (hq : q ∈ G.W) : G.MassivelyReused (G.curve q) := by
  let H := auxCenterEquiv d
  let q' := H.symm q
  let φ := fun (t : G.I.carrier) p => G.γ t (H p)
  have hHq : H q' = q := H.apply_symm_apply q
  have hf : ∀ t, AnalyticOnNhd ℝ (φ t) (H ⁻¹' G.W) := by
    intro t p hps
    exact (G.parameter_analytic ha _ hps t).comp (H.analyticAt p)
  have hr : ∀ p ∈ H ⁻¹' G.W, BlockRank φ p := by
    intro p hps
    have ht := fun t => (G.parameter_analytic ha _ hps t).differentiableAt
    constructor
    · have he : wDerivative φ p =
          functionDerivative (fun (t : G.I.carrier) u => G.γ t ((H p).1, u)) (H p).2 := by
        rw [wDerivative, functionDerivative_comp _ H p ht H.differentiableAt,
          H.fderiv, functionDerivative_snd_slice _ (H p) ht]
        rfl
      rw [he, ← G.pointSpace_eq_range]
      exact hp _ hps
    · rw [← zero_block_range, functionDerivative_comp _ H p ht H.differentiableAt, H.fderiv]
      change finrank ℝ ((functionDerivative (fun (t : G.I.carrier) => G.γ t) (H p)).comp H.toLinearMap).range = d
      rw [range_comp_eq_of_surjective _ _ H.surjective, ← G.curveSpace_eq_range _ ht]
      exact hc _ hps
  obtain ⟨r, hrr, F, hsrc, _, htar, _, _, _, hcoord, _, hid⟩ :=
    lemma_6_1 φ (H ⁻¹' G.W) (hW.preimage H.continuous) q'
      (by change H q' ∈ G.W; rwa [hHq]) hf hr
  refine ⟨ball q.1 r, ?_, isOpen_ball.measurableSet,
    isOpen_ball.measure_pos (μ := volume) ⟨q.1, mem_ball_self hrr⟩⟩
  intro z hz
  let x : BlockParameters 0 d 2 := (q'.1, z)
  have hx : x ∈ F.source := by
    rw [hsrc, ← ball_prod_same]
    exact ⟨mem_ball_self hrr, hz⟩
  have he : H (F x) = (z, (F x).1.2) := by
    change ((F x).2, (F x).1.2) = _
    rw [(hcoord x).2]
  apply (G.mem_centersOf _ z).mpr
  refine ⟨(F x).1.2, ?_, ?_⟩
  · have hh := htar (F.map_source hx)
    change H (F x) ∈ G.W at hh
    rwa [he] at hh
  · apply Set.image_congr
    intro t ht
    change (t, G.γ t (z, (F x).1.2)) = (t, G.γ t q)
    congr 1
    have hh := hid x hx ⟨t, ht⟩
    change G.γ t (H (F x)) = G.γ t (H q') at hh
    simpa only [he, hHq] using hh

/-- The equal-rank branch of Theorem 1.5. No external mathematical input,
boundedness, or positive auxiliary dimension is required. -/
theorem theorem_1_5_case_equal {d m : ℕ} (G : Family 2 d)
    (hWne : G.W.Nonempty) (hW : IsOpen G.W) (ha : G.IsAnalytic)
    (hr : ConstantRanks G m m) : G.AdmitsNikodym ∧ G.HasMassiveCurveReuse := by
  obtain ⟨q, hq⟩ := hWne
  obtain ⟨W₁, _, _, hsub, Wz, Wu, G', hzO, huO, hqz, hune, _, hprod, hga, hgr, he⟩ :=
    corollary_6_2 G hW ha (fun p hp => (hr p hp).1) (fun p hp => (hr p hp).2) q hq
  obtain ⟨u, hu⟩ := hune
  have hnew : G'.HasMassiveCurveReuse :=
    ⟨G'.curve (q.1, u), full_equal_ranks_massive G' (hprod ▸ hzO.prod huO) hga
      (fun p hp => (hgr p hp).1) (fun p hp => (hgr p hp).2)
      (q.1, u) (hprod ▸ ⟨hqz, hu⟩)⟩
  have hold : G.HasMassiveCurveReuse := G'.hasMassiveCurveReuse_mono G (by
    intro z β hβ
    obtain ⟨u, hu, hcurve⟩ := (he z).symm ▸ hβ
    exact ⟨u, hsub hu, hcurve⟩) hnew
  exact ⟨G.admitsNikodym_of_hasMassiveCurveReuse ha.isSmooth hold, hold⟩

end PlanarNikodym
