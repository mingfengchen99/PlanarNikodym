import PlanarNikodym.Reduction.CenterReduction
import PlanarNikodym.Core.ReuseBasics
import PlanarNikodym.Geometry.AnalyticZeros

noncomputable section
open Set Filter Module Metric Function
open scoped Topology
namespace PlanarNikodym

def planarCenterEquiv (j : Fin 2) : Plane ≃L[ℝ] Parameters 2 0 :=
  (show Plane ≃ₗ[ℝ] Parameters 2 0 from
    { toFun := fun p => ((fun i => if i = j then p.2 else p.1), 0)
      invFun := fun p => (p.1 j.rev, p.1 j)
      left_inv := by intro p; fin_cases j <;> simp
      right_inv := by
        intro p
        apply Prod.ext
        · ext i; fin_cases j <;> fin_cases i <;> simp
        · exact Subsingleton.elim _ _
      map_add' := by
        intro p q
        apply Prod.ext
        · ext i; by_cases hi : i = j <;> simp [hi]
        · exact Subsingleton.elim _ _
      map_smul' := by
        intro s p
        apply Prod.ext
        · ext i; by_cases hi : i = j <;> simp [hi]
        · exact Subsingleton.elim _ _ }).toContinuousLinearEquiv

@[simp] theorem planarCenterEquiv_other (j : Fin 2) (p : Plane) :
    (planarCenterEquiv j p).1 j.rev = p.1 := by fin_cases j <;> simp [planarCenterEquiv]

@[simp] theorem planarCenterEquiv_symm (j : Fin 2) (p : Parameters 2 0) :
    (planarCenterEquiv j).symm p = (p.1 j.rev, p.1 j) := rfl

theorem planarCenterEquiv_slice (j : Fin 2) (q : Parameters 2 0) (p : Plane) :
    centerSlice j q (planarCenterEquiv j p) =
      planarCenterEquiv j (((planarCenterEquiv j).symm q).1, p.2) := by
  apply Prod.ext
  · ext i; fin_cases j <;> fin_cases i <;> simp [centerSlice, planarCenterEquiv]
  · rfl

structure RankOneChart (G : Family 2 0) where
  K : Plane ≃L[ℝ] Base 2
  F : OpenPartialHomeomorph Plane Plane
  base : Plane
  radius : ℝ
  radius_pos : 0 < radius
  source_eq : F.source = ball base.1 radius ×ˢ ball base.2 radius
  target_subset : ∀ p ∈ F.target, (K p, 0) ∈ G.W
  analytic : AnalyticOnNhd ℝ F F.source
  inverse_analytic : AnalyticOnNhd ℝ F.symm F.target
  keep_first : ∀ p, (F p).1 = p.1
  normalize : ∀ p ∈ F.source, p.1 = base.1 → F p = p
  h : Plane → ℝ
  h_analytic : AnalyticOnNhd ℝ h (G.I.carrier ×ˢ ball base.2 radius)
  h_nontrivial : ∀ s ∈ ball base.2 radius, ∃ t ∈ G.I.carrier, partialParameter h (t, s) ≠ 0
  identity : ∀ p ∈ F.source, ∀ t ∈ G.I.carrier, G.γ t (K (F p), 0) = h (t, p.2)

theorem scalar_function_rank_one_nonzero {X : Type*} (g : X → ℝ → ℝ) (s : ℝ)
    (hr : finrank ℝ (functionDerivative g s).range = 1) : ∃ t, deriv (g t) s ≠ 0 := by
  by_contra hn
  push Not at hn
  have h1 : functionDerivative g s 1 = 0 := funext hn
  have hz : functionDerivative g s = 0 := by
    apply LinearMap.ext
    intro v
    have hv : v = v • (1 : ℝ) := by simp
    rw [hv, map_smul, h1]
    simp
  have hr0 : finrank ℝ (functionDerivative g s).range = 0 := by
    rw [hz]
    rw [LinearMap.range_zero]
    simp
  omega

theorem exists_rank_one_chart (G : Family 2 0) (hW : IsOpen G.W) (ha : G.IsAnalytic)
    (hc : ∀ p ∈ G.W, G.curveRank p = 1) (q : Parameters 2 0) (hq : q ∈ G.W) :
    ∃ C : RankOneChart G, C.K (C.F C.base) = q.1 := by
  obtain ⟨j, E, hqE, hsW, htW, hEa, hEia, hkeep, hnorm, hid⟩ :=
    corollary_6_3 G hW ha (fun p _ => G.pointRank_zero_aux p)
      (fun p hp => by simpa using hc p hp) q hq
  let L := planarCenterEquiv j
  let b := L.symm q
  let F₀ := (L.toHomeomorph.transOpenPartialHomeomorph E).transHomeomorph L.symm.toHomeomorph
  have hF₀ (p : Plane) : F₀ p = L.symm (E (L p)) := rfl
  have hF₀i (p : Plane) : F₀.symm p = L.symm (E.symm (L p)) := rfl
  have hb : b ∈ F₀.source := by change L b ∈ E.source; simpa only [b, L.apply_symm_apply] using hqE
  have hFa : AnalyticOnNhd ℝ F₀ F₀.source := by
    intro p hp
    exact (L.symm.analyticAt _).comp (f := fun p => E (L p))
      ((hEa _ hp).comp (L.analyticAt p))
  have hFia : AnalyticOnNhd ℝ F₀.symm F₀.target := by
    intro p hp
    exact (L.symm.analyticAt _).comp (f := fun p => E.symm (L p))
      ((hEia _ hp).comp (L.analyticAt p))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (F₀.open_source.mem_nhds hb)
  let F := F₀.restr (ball b r)
  have hs : F.source = ball b r := by
    rw [F₀.restr_source' _ isOpen_ball, inter_eq_right.mpr hball]
  have hsub : F.source ⊆ F₀.source := by rw [hs]; exact hball
  have htsub : F.target ⊆ F₀.target := by intro p hp; exact (F₀.restr_target _ ▸ hp).1
  have hFnorm (p : Plane) (hp : p ∈ F.source) (he : p.1 = b.1) : F p = p := by
    have hpE : L p ∈ E.source := hsub hp
    change L.symm (E (L p)) = p
    rw [hnorm _ hpE]
    · exact L.symm_apply_apply p
    · change p.1 = q.1 j.rev at he
      simpa only [L, planarCenterEquiv_other] using he
  have hFkeep (p : Plane) : (F p).1 = p.1 := by
    change (E (L p)).1 j.rev = p.1
    rw [hkeep, planarCenterEquiv_other]
  have hFE (p : Plane) : L (F p) = E (L p) := by
    change L (L.symm (E (L p))) = _
    exact L.apply_symm_apply _
  have hbase : b ∈ F.source := by rw [hs]; exact mem_ball_self hr
  let K := L.trans (ContinuousLinearEquiv.prodUnique ℝ (Base 2) (Aux 0))
  have hL (p : Plane) : L p = (K p, 0) := by
    apply Prod.ext
    · rfl
    · exact Subsingleton.elim _ _
  let h : Plane → ℝ := fun p => G.γ p.1 (L (b.1, p.2))
  have hline (s : ℝ) (hsr : s ∈ ball b.2 r) : (b.1, s) ∈ F.source := by
    rw [hs, ← ball_prod_same]
    exact ⟨mem_ball_self hr, hsr⟩
  have hWline (s : ℝ) (hsr : s ∈ ball b.2 r) : L (b.1, s) ∈ G.W :=
    hsW (hsub (hline s hsr))
  have hha : AnalyticOnNhd ℝ h (G.I.carrier ×ˢ ball b.2 r) := by
    intro p hp
    exact (ha (p.1, L (b.1, p.2)) ⟨hp.1, hWline _ hp.2⟩).comp
      (f := fun x : Plane => (x.1, L (b.1, x.2)))
      (analyticAt_fst.prod ((L.analyticAt _).comp
        (f := fun x : Plane => (b.1, x.2)) (analyticAt_const.prod analyticAt_snd)))
  have hident (p : Plane) (hp : p ∈ F.source) (t : G.I.carrier) :
      G.γ t (L (F p)) = h (t, p.2) := by
    have hpE : L p ∈ E.source := hsub hp
    have he := hid (L p) hpE t t.property
    rw [planarCenterEquiv_slice] at he
    rw [hFE]
    exact he
  have hhn : ∀ s ∈ ball b.2 r, ∃ t ∈ G.I.carrier, partialParameter h (t, s) ≠ 0 := by
    intro s hsr
    let p : Plane := (b.1, s)
    have hp : p ∈ F.source := hline s hsr
    have hFp : F p = p := hFnorm p hp rfl
    let H : Plane → Parameters 2 0 := fun x => L (F x)
    let g := fun (t : G.I.carrier) s => h (t, s)
    have hHW : H p ∈ G.W := by
      change L (F p) ∈ G.W
      rw [hFE]
      exact htW (E.map_source (show L p ∈ E.source from hsub hp))
    have hf : ∀ t : G.I.carrier, DifferentiableAt ℝ (G.γ t) (H p) := by
      intro t
      exact (G.parameter_analytic ha _ hHW t).differentiableAt
    have hg : ∀ t, DifferentiableAt ℝ (g t) s := by
      intro t
      exact ((hha (t, s) ⟨t.property, hsr⟩).comp
        (f := fun s : ℝ => ((t : ℝ), s)) (analyticAt_const.prod analyticAt_id)).differentiableAt
    have hFap : AnalyticAt ℝ F p := hFa p (hsub hp)
    have hFi : AnalyticOnNhd ℝ F.symm F.target := fun x hx => hFia x (htsub hx)
    have hdf : Surjective (fderiv ℝ F p) := by
      obtain ⟨A, hA⟩ := chart_fderiv_invertible F (fun x hx => hFa x (hsub hx)) hFi p hp
      rw [← hA]
      exact A.surjective
    have hH : DifferentiableAt ℝ H p := L.differentiableAt.comp p hFap.differentiableAt
    have hsH : Surjective (fderiv ℝ H p) := by
      change Surjective (fderiv ℝ ((L : Plane → Parameters 2 0) ∘ (F : Plane → Plane)) p)
      rw [fderiv_comp p L.differentiableAt hFap.differentiableAt, L.fderiv]
      exact L.surjective.comp hdf
    have hP : DifferentiableAt ℝ (Prod.snd : Plane → ℝ) p := differentiableAt_snd
    have hsP : Surjective (fderiv ℝ (Prod.snd : Plane → ℝ) p) := by
      rw [hasFDerivAt_snd.fderiv]
      exact fun y => ⟨(0, y), rfl⟩
    have hrange := functionDerivative_range_of_factorization
      (fun (t : G.I.carrier) => G.γ t) g H Prod.snd p hf hg hH hP hsH hsP (by
        intro t
        filter_upwards [F.open_source.mem_nhds hp] with x hx
        exact hident x hx t)
    have hrank : finrank ℝ (functionDerivative g s).range = 1 := by
      rw [← hrange, ← G.curveSpace_eq_range _ hf]
      exact hc _ hHW
    obtain ⟨t, ht⟩ := scalar_function_rank_one_nonzero g s hrank
    change deriv (fun r => h ((t : ℝ), r)) s ≠ 0 at ht
    exact ⟨t, t.property, by
      rwa [partialParameter_eq_deriv h (t, s) (hha (t, s) ⟨t.property, hsr⟩).differentiableAt]⟩
  refine ⟨⟨K, F, b, r, hr, ?_, ?_, fun p hp => hFa p (hsub hp),
    fun p hp => hFia p (htsub hp), hFkeep, hFnorm, h, hha, hhn, ?_⟩, ?_⟩
  · rw [hs, ball_prod_same]
  · intro p hp
    have hpE : L p ∈ E.target := htsub hp
    have hmem := htW hpE
    rwa [hL] at hmem
  · intro p hp t ht
    rw [← hL]
    exact hident p hp ⟨t, ht⟩
  · rw [hFnorm b hbase rfl]
    exact congrArg Prod.fst (L.apply_symm_apply q)

end PlanarNikodym
