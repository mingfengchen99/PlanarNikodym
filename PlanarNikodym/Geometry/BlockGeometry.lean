import PlanarNikodym.Geometry.LeafTrivialization
import PlanarNikodym.Geometry.RankTransport
import PlanarNikodym.Geometry.CoordinateSelection

noncomputable section
open Set Filter Submodule Module Metric
open scoped Topology
namespace PlanarNikodym

theorem wDerivative_eq_slice {X : Type*} {a b c : ℕ}
    (φ : X → BlockParameters a b c → ℝ) (p : BlockParameters a b c)
    (hf : ∀ t, DifferentiableAt ℝ (φ t) p) :
    wDerivative φ p =
      functionDerivative (fun t w => φ t ((p.1.1, w), p.2)) p.1.2 := by
  symm
  rw [functionDerivative_comp _ _ _ hf (hasFDerivAt_wInsert p).differentiableAt,
    (hasFDerivAt_wInsert p).fderiv]
  rfl

def blockCoordinateEquiv {a b c d : ℕ} (e : (Aux b × Aux c) ≃L[ℝ] Aux d) :
    BlockParameters a b c ≃L[ℝ] Parameters a d :=
  (ContinuousLinearEquiv.prodAssoc ℝ (Aux a) (Aux b) (Aux c)).trans
    ((ContinuousLinearEquiv.refl ℝ (Aux a)).prodCongr e)

@[simp] theorem blockCoordinateEquiv_apply {a b c d : ℕ}
    (e : (Aux b × Aux c) ≃L[ℝ] Aux d) (p : BlockParameters a b c) :
    blockCoordinateEquiv e p = (p.1.1, e (p.1.2, p.2)) := rfl

theorem wDerivative_coordinates {X : Type*} {a b c d : ℕ}
    (f : X → Parameters a d → ℝ) (e : (Aux b × Aux c) ≃L[ℝ] Aux d)
    (p : BlockParameters a b c) (hf : ∀ t, DifferentiableAt ℝ (f t) (blockCoordinateEquiv e p)) :
    wDerivative (fun t s => f t (blockCoordinateEquiv e s)) p =
      (functionDerivative (fun t u => f t (p.1.1, u)) (e (p.1.2, p.2))).comp
        (e.toLinearMap.comp (LinearMap.inl ℝ (Aux b) (Aux c))) := by
  change wDerivative _ p =
    (functionDerivative (fun t u => f t ((blockCoordinateEquiv e p).1, u))
      (blockCoordinateEquiv e p).2).comp _
  rw [wDerivative, functionDerivative_comp _ _ _ hf (blockCoordinateEquiv e).differentiableAt,
    functionDerivative_snd_slice _ (blockCoordinateEquiv e p) hf]
  simp only [ContinuousLinearEquiv.fderiv]
  rfl

theorem vertical_range_coordinates {X : Type*} {a b c d : ℕ}
    (f : X → Parameters a d → ℝ) (e : (Aux b × Aux c) ≃L[ℝ] Aux d)
    (p : BlockParameters a b c) (hf : ∀ t, DifferentiableAt ℝ (f t) (blockCoordinateEquiv e p)) :
    (wDerivative (fun t s => f t (blockCoordinateEquiv e s)) p).range ⊔
      (etaDerivative (fun t s => f t (blockCoordinateEquiv e s)) p).range =
        (functionDerivative (fun t u => f t (p.1.1, u)) (e (p.1.2, p.2))).range := by
  let L := functionDerivative (fun t u => f t (p.1.1, u)) (e (p.1.2, p.2))
  have hη : etaDerivative (fun t s => f t (blockCoordinateEquiv e s)) p =
      L.comp (e.toLinearMap.comp (LinearMap.inr ℝ (Aux b) (Aux c))) := by
    rw [etaDerivative, functionDerivative_comp _ _ _ hf (blockCoordinateEquiv e).differentiableAt]
    change _ =
      (functionDerivative (fun t u => f t ((blockCoordinateEquiv e p).1, u))
        (blockCoordinateEquiv e p).2).comp _
    rw [functionDerivative_snd_slice _ (blockCoordinateEquiv e p) hf]
    simp only [ContinuousLinearEquiv.fderiv]
    rfl
  rw [wDerivative_coordinates f e p hf, hη]
  change ((L.comp e.toLinearMap).comp (LinearMap.inl ℝ (Aux b) (Aux c))).range ⊔
    ((L.comp e.toLinearMap).comp (LinearMap.inr ℝ (Aux b) (Aux c))).range = L.range
  rw [← range_prod_decomposition, range_comp_eq_of_surjective _ _ e.surjective]

theorem restrict_eta_range {X : Type*} {a b c : ℕ}
    (φ : X → BlockParameters a b c → ℝ) (p : BlockParameters a b c)
    (hf : ∀ t, DifferentiableAt ℝ (φ t) p) (hr : BlockRank φ p) :
    (functionDerivative φ p).range =
      (functionDerivative (fun t v => φ t (v, p.2)) p.1).range := by
  rw [functionDerivative_fst_slice _ p hf]
  have hw : (wDerivative φ p).range ≤
      ((functionDerivative φ p).comp
        (ContinuousLinearMap.inl ℝ (Aux a × Aux b) (Aux c)).toLinearMap).range := by
    rintro g ⟨w, rfl⟩
    exact ⟨(0, w), rfl⟩
  have hη := (block_rank_range_le φ p hr).trans hw
  conv_lhs => rw [range_prod_decomposition]
  apply sup_eq_left.mpr
  exact hη

theorem wDerivative_rank_near {X : Type*} {a b c : ℕ}
    (φ : X → BlockParameters a b c → ℝ) (q : BlockParameters a b c)
    (hf : ∀ t, AnalyticAt ℝ (φ t) q)
    (hi : Function.Injective (wDerivative φ q)) :
    ∀ᶠ p in 𝓝 q, finrank ℝ (wDerivative φ p).range = b := by
  have hr : finrank ℝ (wDerivative φ q).range = b := by
    simpa using LinearMap.finrank_range_of_inj hi
  have hli := independent_of_rank_eq (fun j => wDerivative φ q (Pi.single j 1))
    (by rw [← range_eq_span_coordinates]; exact hr)
  obtain ⟨x, hx⟩ := exists_eval_det_ne_zero _ hli
  have hd := compensator_det_near φ x (fun p => p.1.2) q
    (fun i => hf (x i))
    (analyticAt_snd.comp analyticAt_fst) rfl hx
  filter_upwards [hd] with p hp
  have hp' : Matrix.det (fun i j => wDerivative φ p (Pi.single j 1) (x i)) ≠ 0 := by
    simpa only [compensated, Prod.eta] using hp
  rw [range_eq_span_coordinates]
  exact (finrank_span_eq_card (independent_of_eval_det_ne_zero _ _ hp')).trans (Fintype.card_fin b)

end PlanarNikodym
