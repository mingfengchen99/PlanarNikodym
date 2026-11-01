import PlanarNikodym.Cells.AnalyticPieces
import PlanarNikodym.Geometry.RankTransport
import PlanarNikodym.Reduction.FamilyReduction

noncomputable section
open Set Filter Submodule Module
open scoped Topology
namespace PlanarNikodym

/-- A surjective derivative of a centre-preserving map is surjective on
vertical directions as well. No inverse differentiability is inferred from
the existence of a continuous inverse. -/
theorem vertical_derivative_surjective {A B C : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    (H : A × B → A × C) (q : A × B) (hH : DifferentiableAt ℝ H q)
    (hc : (fun x => (H x).1) =ᶠ[𝓝 q] Prod.fst)
    (hs : Function.Surjective (fderiv ℝ H q)) :
    Function.Surjective (fderiv ℝ (fun v => (H (q.1, v)).2) q.2) := by
  have hfst : (ContinuousLinearMap.fst ℝ A C).comp (fderiv ℝ H q) =
      ContinuousLinearMap.fst ℝ A B :=
    ((hH.hasFDerivAt.fst).congr_of_eventuallyEq hc.symm).unique hasFDerivAt_fst
  have haux : fderiv ℝ (fun v => (H (q.1, v)).2) q.2 =
      ((ContinuousLinearMap.snd ℝ A C).comp (fderiv ℝ H q)).comp
        (ContinuousLinearMap.inr ℝ A B) := by
    rw [fderiv_snd_slice (fun x => (H x).2) q hH.snd, hH.hasFDerivAt.snd.fderiv]
  intro v
  obtain ⟨w, hw⟩ := hs (0, v)
  have hw0 : w.1 = 0 := by
    have he := congrArg (fun L : (A × B) →L[ℝ] A => L w) hfst
    simpa [hw] using he.symm
  refine ⟨w.2, ?_⟩
  rw [haux]
  change (fderiv ℝ H q (0, w.2)).2 = v
  have he : (0, w.2) = w := Prod.ext hw0.symm rfl
  rw [he, hw]

theorem functionDerivative_congr_germ {X E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : X → E → ℝ) (p : E) (he : ∀ t, f t =ᶠ[𝓝 p] g t) :
    functionDerivative f p = functionDerivative g p := by
  ext v t
  exact congrArg (fun L : E →L[ℝ] ℝ => L v) ((he t).fderiv_eq (𝕜 := ℝ))

/-- The vertical function-derivative image is unchanged by a regular
centre-preserving parameter change. -/
theorem vertical_functionDerivative_range {X A B C : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    (f : X → A × C → ℝ) (H : A × B → A × C) (q : A × B)
    (hf : ∀ t, DifferentiableAt ℝ (f t) (H q))
    (hH : DifferentiableAt ℝ H q)
    (hc : (fun x => (H x).1) =ᶠ[𝓝 q] Prod.fst)
    (hs : Function.Surjective (fderiv ℝ H q)) :
    (functionDerivative (fun t v => f t (H (q.1, v))) q.2).range =
      (functionDerivative (fun t u => f t ((H q).1, u)) (H q).2).range := by
  let U : B → C := fun v => (H (q.1, v)).2
  have hq : (H q).1 = q.1 := hc.eq_of_nhds
  have hslice : ∀ t, DifferentiableAt ℝ (fun u => f t ((H q).1, u)) (U q.2) :=
    fun t => (hf t).comp (H q).2 ((differentiableAt_const _).prodMk differentiableAt_id)
  have hU : DifferentiableAt ℝ U q.2 :=
    (hH.comp q.2 ((differentiableAt_const q.1).prodMk differentiableAt_id)).snd
  have hEq : ∀ t, (fun v => f t (H (q.1, v))) =ᶠ[𝓝 q.2]
      (fun v => f t ((H q).1, U v)) := by
    intro t
    have he := (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds hc
    filter_upwards [he] with v hv
    exact congrArg (f t) (Prod.ext (hv.trans hq.symm) rfl)
  rw [functionDerivative_congr_germ _ _ _ hEq,
    functionDerivative_comp _ U q.2 hslice hU,
    range_comp_eq_of_surjective _ _ (vertical_derivative_surjective H q hH hc hs)]

/-- Both actual function ranks are invariant under a regular,
centre-preserving analytic parametrization. The intervals need only agree,
and identities are needed only on the open parameter domain. -/
theorem Family.ranks_of_parameter_change {d e : ℕ} (G : Family 2 d) (H : Family 2 e)
    (hI : H.I = G.I) (hO : IsOpen H.W) (hG : G.IsAnalytic) (hH : H.IsAnalytic)
    (Φ : Parameters 2 e → Parameters 2 d) (q : Parameters 2 e) (hq : q ∈ H.W)
    (hm : Φ q ∈ G.W) (hd : DifferentiableAt ℝ Φ q)
    (hc : ∀ p ∈ H.W, (Φ p).1 = p.1)
    (hi : ∀ p ∈ H.W, ∀ t ∈ G.I.carrier, H.γ t p = G.γ t (Φ p))
    (hs : Function.Surjective (fderiv ℝ Φ q)) :
    H.pointRank q = G.pointRank (Φ q) ∧ H.curveRank q = G.curveRank (Φ q) := by
  rcases G with ⟨I, W, γ⟩
  rcases H with ⟨J, V, φ⟩
  dsimp only at hI
  subst J
  let G : Family 2 d := ⟨I, W, γ⟩
  let H : Family 2 e := ⟨I, V, φ⟩
  have hfg : ∀ t : I.carrier, DifferentiableAt ℝ (γ t) (Φ q) :=
    fun t => (G.parameter_analytic hG (Φ q) hm t).differentiableAt
  have hfh : ∀ t : I.carrier, DifferentiableAt ℝ (φ t) q :=
    fun t => (H.parameter_analytic hH q hq t).differentiableAt
  have he : ∀ t : I.carrier, φ t =ᶠ[𝓝 q] (fun p => γ t (Φ p)) := by
    intro t
    filter_upwards [hO.mem_nhds hq] with p hp
    exact hi p hp t t.property
  have hec : (fun p => (Φ p).1) =ᶠ[𝓝 q] Prod.fst := by
    filter_upwards [hO.mem_nhds hq] with p hp
    exact hc p hp
  constructor
  · change finrank ℝ (H.pointSpace q) = finrank ℝ (G.pointSpace (Φ q))
    rw [H.pointSpace_eq_range, G.pointSpace_eq_range]
    have hv : ∀ t : I.carrier, (fun v => φ t (q.1, v)) =ᶠ[𝓝 q.2]
        (fun v => γ t (Φ (q.1, v))) := by
      intro t
      exact (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (he t)
    rw [functionDerivative_congr_germ _ _ _ hv,
      vertical_functionDerivative_range (fun (t : I.carrier) => γ t) Φ q hfg hd hec hs]
  · change finrank ℝ (H.curveSpace q) = finrank ℝ (G.curveSpace (Φ q))
    rw [H.curveSpace_eq_range q hfh, G.curveSpace_eq_range (Φ q) hfg,
      functionDerivative_congr_germ _ _ _ he, functionDerivative_comp _ Φ q hfg hd,
      range_comp_eq_of_surjective _ _ hs]

theorem AnalyticPiece.ranks_eq_of_surjective {d : ℕ} {G : Family 2 d}
    (P : AnalyticPiece G) (hG : G.IsAnalytic) (q : Parameters 2 P.dim)
    (hq : q ∈ P.family.W) (hs : Function.Surjective (fderiv ℝ P.embed q)) :
    P.family.pointRank q = G.pointRank (P.embed q) ∧
      P.family.curveRank q = G.curveRank (P.embed q) :=
  G.ranks_of_parameter_change P.family P.interval_eq P.open_domain hG P.analytic_family
    P.embed q hq (P.maps_to q hq) (P.analytic_embed q hq).differentiableAt
    P.keep_center P.identity hs

end PlanarNikodym
