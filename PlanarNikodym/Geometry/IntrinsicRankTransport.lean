import PlanarNikodym.Cells.CellRankTransport
import PlanarNikodym.Rank.ConstrainedRank

/-! Actual point/curve ranks in a centre chart are the function ranks on
the embedded tangent and its centre kernel. Ambient surjectivity is not
required and is not inferred from immersion. -/
noncomputable section
open Set Filter Submodule Module
open scoped Topology
namespace PlanarNikodym

theorem vertical_range_eq_tangent_inf_ker {A B E : Type*}
    [AddCommGroup A] [Module ℝ A] [AddCommGroup B] [Module ℝ B]
    [AddCommGroup E] [Module ℝ E]
    (J : A × B →ₗ[ℝ] E) (L : E →ₗ[ℝ] A)
    (hc : L.comp J = LinearMap.fst ℝ A B) :
    (J.comp (LinearMap.inr ℝ A B)).range = J.range ⊓ L.ker := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨⟨(0, u), rfl⟩, ?_⟩
    have he := congrArg (fun f : (A × B) →ₗ[ℝ] A => f (0, u)) hc
    exact he
  · rintro ⟨⟨q, rfl⟩, hq⟩
    have he := congrArg (fun f : (A × B) →ₗ[ℝ] A => f q) hc
    have hq0 : q.1 = 0 := he.symm.trans hq
    refine ⟨q.2, ?_⟩
    change J (0, q.2) = J q
    rw [show (0, q.2) = q from Prod.ext hq0.symm rfl]

def Family.tangentCurveRank {d : ℕ} (G : Family 2 d) (p : Parameters 2 d)
    (T : Submodule ℝ (Parameters 2 d)) : ℕ :=
  finrank ℝ ((functionDerivative (fun (t : G.I.carrier) => G.γ t) p).domRestrict T).range

def Family.tangentPointRank {d : ℕ} (G : Family 2 d) (p : Parameters 2 d)
    (T : Submodule ℝ (Parameters 2 d)) : ℕ :=
  finrank ℝ ((functionDerivative (fun (t : G.I.carrier) => G.γ t) p).domRestrict
    (T ⊓ (LinearMap.fst ℝ (Base 2) (Aux d)).ker)).range

theorem Family.ranks_of_tangent_parameter_change {d e : ℕ} (G : Family 2 d) (H : Family 2 e)
    (hI : H.I = G.I) (hO : IsOpen H.W) (hG : G.IsAnalytic) (hH : H.IsAnalytic)
    (Φ : Parameters 2 e → Parameters 2 d) (q : Parameters 2 e) (hq : q ∈ H.W)
    (hm : Φ q ∈ G.W) (hd : DifferentiableAt ℝ Φ q)
    (hc : ∀ p ∈ H.W, (Φ p).1 = p.1)
    (hi : ∀ p ∈ H.W, ∀ t ∈ G.I.carrier, H.γ t p = G.γ t (Φ p))
    (T : Submodule ℝ (Parameters 2 d)) (hT : (fderiv ℝ Φ q).toLinearMap.range = T) :
    H.pointRank q = G.tangentPointRank (Φ q) T ∧
      H.curveRank q = G.tangentCurveRank (Φ q) T := by
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
  have hcenter : (LinearMap.fst ℝ (Base 2) (Aux d)).comp
      (fderiv ℝ Φ q).toLinearMap = LinearMap.fst ℝ (Base 2) (Aux e) := by
    have heq := ((hd.hasFDerivAt.fst).congr_of_eventuallyEq hec.symm).unique hasFDerivAt_fst
    exact congrArg ContinuousLinearMap.toLinearMap heq
  have hvertical := vertical_range_eq_tangent_inf_ker (fderiv ℝ Φ q).toLinearMap
    (LinearMap.fst ℝ (Base 2) (Aux d)) hcenter
  rw [hT] at hvertical
  have hder := functionDerivative_congr_germ _ _ _ he
  rw [functionDerivative_comp _ Φ q hfg hd] at hder
  constructor
  · change finrank ℝ (H.pointSpace q) = G.tangentPointRank (Φ q) T
    rw [H.pointSpace_eq_range, functionDerivative_snd_slice _ q hfh, hder]
    change finrank ℝ (((functionDerivative (fun (t : I.carrier) => γ t) (Φ q)).comp
      (fderiv ℝ Φ q).toLinearMap).comp (LinearMap.inr ℝ (Base 2) (Aux e))).range = _
    rw [LinearMap.comp_assoc, range_comp_eq_map_of_range_eq _ _ _ hvertical]
    rfl
  · change finrank ℝ (H.curveSpace q) = G.tangentCurveRank (Φ q) T
    rw [H.curveSpace_eq_range q hfh, hder, range_comp_eq_map_of_range_eq _ _ _ hT]
    rfl

theorem AnalyticPiece.ranks_eq_intrinsic {d : ℕ} {G : Family 2 d}
    (P : AnalyticPiece G) (hG : G.IsAnalytic) (q : Parameters 2 P.dim) (hq : q ∈ P.family.W)
    (T : Submodule ℝ (Parameters 2 d)) (hT : (fderiv ℝ P.embed q).toLinearMap.range = T) :
    P.family.pointRank q = G.tangentPointRank (P.embed q) T ∧
      P.family.curveRank q = G.tangentCurveRank (P.embed q) T :=
  G.ranks_of_tangent_parameter_change P.family P.interval_eq P.open_domain hG P.analytic_family
    P.embed q hq (P.maps_to q hq) (P.analytic_embed q hq).differentiableAt
    P.keep_center P.identity T hT

end PlanarNikodym
