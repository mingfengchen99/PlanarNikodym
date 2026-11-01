import PlanarNikodym.Reduction.FamilyReduction

noncomputable section
open Set Filter Submodule Module Metric
open scoped Topology
namespace PlanarNikodym

/-- Separate a chosen effective centre direction, the auxiliary variables,
and the other centre direction. The unused zero-dimensional block is explicit. -/
def centerBlockEquiv (d : ℕ) (j : Fin 2) :
    BlockParameters 0 (d + 1) 1 ≃L[ℝ] Parameters 2 d :=
  (show BlockParameters 0 (d + 1) 1 ≃ₗ[ℝ] Parameters 2 d from
    { toFun := fun p => ((fun i => if i = j then p.1.2 0 else p.2 0), Fin.tail p.1.2)
      invFun := fun p => ((0, Fin.cons (p.1 j) p.2), fun _ => p.1 j.rev)
      left_inv := by
        intro p
        apply Prod.ext
        · apply Prod.ext
          · exact Subsingleton.elim _ _
          · ext i
            refine Fin.cases ?_ (fun k => ?_) i
            · simp
            · rfl
        · ext i
          fin_cases i
          fin_cases j <;> simp
      right_inv := by
        intro p
        apply Prod.ext
        · ext i
          fin_cases j <;> fin_cases i <;> simp
        · rfl
      map_add' := by
        intro x y
        apply Prod.ext
        · ext i
          by_cases hi : i = j <;> simp [hi]
        · rfl
      map_smul' := by
        intro s x
        apply Prod.ext
        · ext i
          by_cases hi : i = j <;> simp [hi]
        · rfl }).toContinuousLinearEquiv

@[simp] theorem centerBlockEquiv_apply {d : ℕ} (j : Fin 2)
    (p : BlockParameters 0 (d + 1) 1) :
    centerBlockEquiv d j p =
      ((fun i => if i = j then p.1.2 0 else p.2 0), Fin.tail p.1.2) := rfl

@[simp] theorem centerBlockEquiv_symm_apply {d : ℕ} (j : Fin 2) (p : Parameters 2 d) :
    (centerBlockEquiv d j).symm p = ((0, Fin.cons (p.1 j) p.2), fun _ => p.1 j.rev) := rfl

theorem centerBlockEquiv_other {d : ℕ} (j : Fin 2)
    (p : BlockParameters 0 (d + 1) 1) : (centerBlockEquiv d j p).1 j.rev = p.2 0 := by
  fin_cases j <;> simp

theorem Family.exists_transverse_center {d : ℕ} (G : Family 2 d) (q : Parameters 2 d)
    (hp : G.pointRank q = d) (hc : G.curveRank q = d + 1) :
    ∃ j : Fin 2, G.zColumn q j ∉ G.pointSpace q := by
  by_contra hn
  push Not at hn
  have he : G.curveSpace q = G.pointSpace q := by
    apply sup_eq_left.mpr
    exact span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hn j)
  have hr : G.curveRank q = G.pointRank q :=
    congrArg (fun S : Submodule ℝ (G.I.carrier → ℝ) => finrank ℝ S) he
  omega

theorem injective_of_full_range_rank {V : Type*} [AddCommGroup V] [Module ℝ V]
    {d : ℕ} (L : Aux d →ₗ[ℝ] V) (hr : finrank ℝ L.range = d) :
    Function.Injective L := by
  have h := L.finrank_range_add_finrank_ker
  rw [hr] at h
  have hk : finrank ℝ L.ker = 0 := by simpa using h
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

theorem center_wDerivative_injective {d : ℕ} (G : Family 2 d) (q : Parameters 2 d)
    (hf : ∀ t : G.I.carrier, DifferentiableAt ℝ (G.γ t) q)
    (hp : G.pointRank q = d) (j : Fin 2) (hj : G.zColumn q j ∉ G.pointSpace q) :
    Function.Injective (wDerivative
      (fun (t : G.I.carrier) p => G.γ t (centerBlockEquiv d j p))
      ((centerBlockEquiv d j).symm q)) := by
  let H := centerBlockEquiv d j
  let q' := H.symm q
  let L := functionDerivative (fun (t : G.I.carrier) u => G.γ t (q.1, u)) q.2
  have hLr : L.range = G.pointSpace q := (G.pointSpace_eq_range q).symm
  have hLi : Function.Injective L := injective_of_full_range_rank L (hLr ▸ hp)
  let A := wDerivative (fun (t : G.I.carrier) p => G.γ t (H p)) q'
  have hA (w : Aux (d + 1)) : A w = w 0 • G.zColumn q j + L (Fin.tail w) := by
    dsimp only [A]
    rw [wDerivative, functionDerivative_comp _ H q'
      (by simpa only [q', H.apply_symm_apply] using hf) H.differentiableAt, H.fderiv]
    simp only [q', H.apply_symm_apply]
    change functionDerivative (fun (t : G.I.carrier) p => G.γ t p) q
      (H (wIn 0 (d + 1) 1 w)) = _
    have hs : H (wIn 0 (d + 1) 1 w) =
        (w 0 • Pi.single j 1, 0) + (0, Fin.tail w) := by
      apply Prod.ext
      · ext i
        simp [H, wIn, Pi.single_apply, eq_comm]
      · simp [H, wIn]
    rw [hs, map_add]
    have hz := congrArg (fun M : Aux 2 →ₗ[ℝ] (G.I.carrier → ℝ) => M (w 0 • Pi.single j 1))
      (functionDerivative_fst_slice (fun (t : G.I.carrier) p => G.γ t p) q hf)
    have hu := congrArg (fun M : Aux d →ₗ[ℝ] (G.I.carrier → ℝ) => M (Fin.tail w))
      (functionDerivative_snd_slice (fun (t : G.I.carrier) p => G.γ t p) q hf)
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply] at hz hu
    rw [← hz, ← hu, map_smul]
    rfl
  change Function.Injective A
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro w hw
  change A w = 0 at hw
  have he : w 0 • G.zColumn q j + L (Fin.tail w) = 0 := by
    rw [← hA]
    exact hw
  have ha : w 0 = 0 := by
    by_contra hn
    apply hj
    have hmem : w 0 • G.zColumn q j ∈ G.pointSpace q := by
      rw [eq_neg_of_add_eq_zero_left he, ← hLr]
      exact Submodule.neg_mem _ ⟨Fin.tail w, rfl⟩
    exact (Submodule.smul_mem_iff _ hn).mp hmem
  have hu : Fin.tail w = 0 := by
    apply hLi
    simpa only [ha, zero_smul, zero_add, map_zero] using he
  show w = 0
  ext i
  refine Fin.cases ha (fun k => congrFun hu k) i

end PlanarNikodym
