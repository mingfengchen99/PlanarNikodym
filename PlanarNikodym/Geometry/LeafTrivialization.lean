import PlanarNikodym.Projection.CompensationRigidity

noncomputable section
open Set Filter Submodule Module Metric
open scoped Topology ContDiff Matrix
namespace PlanarNikodym

theorem compensated_preserves_on_box {X : Type*} {a b c : ℕ}
    (φ : X → BlockParameters a b c → ℝ) (κ : BlockParameters a b c → Aux b)
    (q : BlockParameters a b c) (r : ℝ) (hr : 0 < r) (x : Fin b → X)
    (hκ : AnalyticOnNhd ℝ κ (ball q.1 r ×ˢ ball q.2 r))
    (hf : ∀ p ∈ ball q.1 r ×ˢ ball q.2 r, ∀ t,
      AnalyticAt ℝ (φ t) (compensated κ p))
    (hrank : ∀ p ∈ ball q.1 r ×ˢ ball q.2 r, BlockRank φ (compensated κ p))
    (hdet : ∀ p ∈ ball q.1 r ×ˢ ball q.2 r,
      Matrix.det (fun i j => wDerivative φ (compensated κ p) (Pi.single j 1) (x i)) ≠ 0)
    (heq : ∀ p ∈ ball q.1 r ×ˢ ball q.2 r, ∀ i,
      φ (x i) (compensated κ p) = φ (x i) (p.1, q.2))
    (hnorm : ∀ v ∈ ball q.1 r, κ (v, q.2) = v.2) :
    ∀ p ∈ ball q.1 r ×ˢ ball q.2 r, ∀ t,
      φ t (compensated κ p) = φ t (p.1, q.2) := by
  intro p hp t
  let ψ := fun η : Aux c => φ t (compensated κ (p.1, η))
  have hψ : ∀ η ∈ ball q.2 r, AnalyticAt ℝ ψ η := by
    intro η hη
    have hm : AnalyticAt ℝ (fun s : Aux c => compensated κ (p.1, s)) η :=
      (compensated_analyticAt κ (p.1, η) (hκ _ ⟨hp.1, hη⟩)).comp
        (f := fun s : Aux c => (p.1, s)) (analyticAt_const.prod analyticAt_id)
    exact (hf (p.1, η) ⟨hp.1, hη⟩ t).comp
      (f := fun s : Aux c => compensated κ (p.1, s)) hm
  have hzero : ∀ η ∈ ball q.2 r, fderiv ℝ ψ η = 0 := by
    intro η hη
    exact compensated_eta_derivative_zero φ κ q.2 _ (isOpen_ball.prod isOpen_ball)
      (p.1, η) ⟨hp.1, hη⟩ x (hκ _ ⟨hp.1, hη⟩)
      (fun s => (hf (p.1, η) ⟨hp.1, hη⟩ s).differentiableAt)
      (hrank _ ⟨hp.1, hη⟩) (hdet _ ⟨hp.1, hη⟩) heq t
  have he : ψ p.2 = ψ q.2 :=
    isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball _ _).isPreconnected
      (fun η hη => (hψ η hη).differentiableAt.differentiableWithinAt)
      hzero hp.2 (mem_ball_self hr)
  simpa only [ψ, compensated, hnorm p.1 hp.1, Prod.eta] using he

/-- Lemma 6.1 for parameter-analytic families, strengthened to an analytic
chart whose source is a ball. This includes b=0 and c=0 without separate assumptions. -/
theorem lemma_6_1 {X : Type*} {a b c : ℕ}
    (φ : X → BlockParameters a b c → ℝ) (W : Set (BlockParameters a b c))
    (hW : IsOpen W) (q : BlockParameters a b c) (hq : q ∈ W)
    (hf : ∀ t, AnalyticOnNhd ℝ (φ t) W)
    (hrank : ∀ p ∈ W, BlockRank φ p) :
    ∃ r : ℝ, 0 < r ∧ ∃ e : OpenPartialHomeomorph (BlockParameters a b c) (BlockParameters a b c),
      e.source = ball q r ∧ e.source ⊆ W ∧ e.target ⊆ W ∧ e q = q ∧
      AnalyticOnNhd ℝ e e.source ∧ AnalyticOnNhd ℝ e.symm e.target ∧
      (∀ p, (e p).1.1 = p.1.1 ∧ (e p).2 = p.2) ∧
      (∀ p ∈ e.source, p.2 = q.2 → e p = p) ∧
      ∀ p ∈ e.source, ∀ t, φ t (e p) = φ t (p.1, q.2) := by
  obtain ⟨x, κ, hκ, hκq, hEq, hNorm, hDet⟩ :=
    exists_compensator φ q (fun t => hf t q hq) (hrank q hq)
  let F := compensated κ
  have hFq : F q = q := by simp [F, compensated, hκq]
  have hFa := compensated_analyticAt κ q hκ
  have hFw : ∀ᶠ p in 𝓝 q, F p ∈ W := by
    have ht := hFa.continuousAt.tendsto
    change Tendsto F (𝓝 q) (𝓝 (F q)) at ht
    rw [hFq] at ht
    exact ht (hW.mem_nhds hq)
  have hDetNear := compensator_det_near φ x κ q (fun i => hf (x i) q hq) hκ hκq hDet
  have hGood : ∀ᶠ p in 𝓝 q, p ∈ W ∧ F p ∈ W ∧ AnalyticAt ℝ κ p ∧
      (∀ i, φ (x i) (F p) = φ (x i) (p.1, q.2)) ∧
      Matrix.det (fun i j => wDerivative φ (F p) (Pi.single j 1) (x i)) ≠ 0 := by
    filter_upwards [hW.mem_nhds hq, hFw, hκ.eventually_analyticAt, hEq, hDetNear]
      with p hp hfp hkp heq hd
    exact ⟨hp, hfp, hkp, heq, hd⟩
  obtain ⟨s, hs, hS⟩ := Metric.mem_nhds_iff.mp hGood
  obtain ⟨s', hs', hS'⟩ := Metric.mem_nhds_iff.mp hNorm
  let R := min s s'
  have hR : 0 < R := lt_min hs hs'
  let U := ball q.1 R ×ˢ ball q.2 R
  have hU : IsOpen U := isOpen_ball.prod isOpen_ball
  have hqU : q ∈ U := ⟨mem_ball_self hR, mem_ball_self hR⟩
  have hUR : ∀ p ∈ U, p ∈ W ∧ F p ∈ W ∧ AnalyticAt ℝ κ p ∧
      (∀ i, φ (x i) (F p) = φ (x i) (p.1, q.2)) ∧
      Matrix.det (fun i j => wDerivative φ (F p) (Pi.single j 1) (x i)) ≠ 0 := by
    intro p hp
    apply hS
    apply ball_subset_ball (min_le_left s s')
    exact (ball_prod_same q.1 q.2 R) ▸ hp
  have hN : ∀ v ∈ ball q.1 R, κ (v, q.2) = v.2 := by
    intro v hv
    exact hS' (ball_subset_ball (min_le_right s s') hv)
  have hPreserve := compensated_preserves_on_box φ κ q R hR x
    (fun p hp => (hUR p hp).2.2.1)
    (fun p hp t => hf t (F p) (hUR p hp).2.1)
    (fun p hp => hrank (F p) (hUR p hp).2.1)
    (fun p hp => (hUR p hp).2.2.2.2)
    (fun p hp => (hUR p hp).2.2.2.1) hN
  obtain ⟨e₀, hqe, heU, heF, hea, heia⟩ := exists_analytic_chart F q hFa
    (compensated_isInvertible κ q hκ hNorm) U (hU.mem_nhds hqU)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (e₀.open_source.mem_nhds hqe)
  let e := e₀.restr (ball q r)
  have hes : e.source = ball q r := by
    rw [e₀.restr_source' _ isOpen_ball, inter_eq_right.mpr hball]
  have he₀ : ∀ p, e p = e₀ p := fun _ => rfl
  have heSub : e.source ⊆ e₀.source := by rw [hes]; exact hball
  have htSub : e.target ⊆ e₀.target := by
    intro y hy
    exact (e₀.restr_target _ ▸ hy).1
  refine ⟨r, hr, e, hes, fun p hp => (hUR p (heU (heSub hp))).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have hx := e.map_target hy
    have hw := (hUR (e.symm y) (heU (heSub hx))).2.1
    have hexy : F (e.symm y) = y := by rw [← heF, ← he₀]; exact e.right_inv hy
    rwa [hexy] at hw
  · rw [he₀, heF, hFq]
  · intro p hp
    exact hea p (heSub hp)
  · intro y hy
    exact heia y (htSub hy)
  · intro p
    simp only [he₀, heF, F, compensated, and_self]
  · intro p hp hpη
    rw [he₀, heF]
    change compensated κ p = p
    have hn : κ p = p.1.2 := by simpa only [← hpη] using hN p.1 (heU (heSub hp)).1
    simp [compensated, hn]
  · intro p hp t
    rw [he₀, heF]
    exact hPreserve p (heU (heSub hp)) t

end PlanarNikodym
