import PlanarNikodym.Classification.IntermediateReuse

noncomputable section
open Set Filter Metric Module Function MeasureTheory
open scoped Topology
namespace PlanarNikodym

/-- (x,w₀,u) ↦ (z,u), with z_j=w₀ and z_{j.rev}=x. -/
def intermediateCoordinates (d : ℕ) (j : Fin 2) :
    (ℝ × Aux (d + 1)) ≃L[ℝ] Parameters 2 d :=
  (show (ℝ × Aux (d + 1)) ≃ₗ[ℝ] Parameters 2 d from
    { toFun := fun p => ((fun i => if i = j then p.2 0 else p.1), Fin.tail p.2)
      invFun := fun p => (p.1 j.rev, Fin.cons (p.1 j) p.2)
      left_inv := by
        intro p
        apply Prod.ext
        · fin_cases j <;> simp
        · ext i; refine Fin.cases ?_ (fun k => ?_) i
          · simp
          · rfl
      right_inv := by
        intro p
        apply Prod.ext
        · ext i; fin_cases j <;> fin_cases i <;> simp
        · rfl
      map_add' := by
        intro p q
        apply Prod.ext
        · ext i; by_cases hi : i = j <;> simp [hi]
        · rfl
      map_smul' := by
        intro s p
        apply Prod.ext
        · ext i; by_cases hi : i = j <;> simp [hi]
        · rfl }).toContinuousLinearEquiv

@[simp] theorem intermediateCoordinates_other {d : ℕ} (j : Fin 2) (p : ℝ × Aux (d + 1)) :
    (intermediateCoordinates d j p).1 j.rev = p.1 := by
  fin_cases j <;> simp [intermediateCoordinates]

theorem intermediateCoordinates_slice {d : ℕ} (j : Fin 2) (q : Parameters 2 d)
    (p : ℝ × Aux (d + 1)) :
    centerSlice j q (intermediateCoordinates d j p) =
      intermediateCoordinates d j (q.1 j.rev, p.2) := by
  apply Prod.ext
  · ext i; fin_cases j <;> fin_cases i <;> simp [centerSlice, intermediateCoordinates]
  · rfl

/-- The scalar projection model used in §7.3. `h` parametrizes the curves;
`κ` parametrizes their centre traces. Its rank is the actual derivative of h
as a map into functions on I, not a supplied matrix of derivative columns. -/
structure ProjectionModel (d : ℕ) where
  I : Interval
  base : ℝ × Aux (d + 1)
  radius : ℝ
  radius_pos : 0 < radius
  h : ℝ → Aux (d + 1) → ℝ
  κ : ℝ × Aux (d + 1) → ℝ
  h_analytic : AnalyticOnNhd ℝ (fun x : ℝ × Aux (d + 1) => h x.1 x.2)
    (I.carrier ×ˢ ball base.2 radius)
  κ_analytic : AnalyticOnNhd ℝ κ (ball base.1 radius ×ˢ ball base.2 radius)
  normalize : ∀ w ∈ ball base.2 radius, κ (base.1, w) = w 0
  h_injective : ∀ w ∈ ball base.2 radius,
    Injective (functionDerivative (fun (t : I.carrier) => h t) w)

namespace ProjectionModel
variable {d : ℕ} (D : ProjectionModel d)

def hitTimes (w : Aux (d + 1)) (E : Set Plane) : Set ℝ :=
  {t | t ∈ D.I.carrier ∧ (t, D.h t w) ∈ E}

def incidenceTrace (E : Set Plane) : Set Plane :=
  {c | ∃ x ∈ ball D.base.1 D.radius, ∃ w ∈ ball D.base.2 D.radius,
    c = (x, D.κ (x, w)) ∧ 0 < volume (D.hitTimes w E)}

def TimeCovered (V : Family.Foliations) (w : Aux (d + 1)) : Prop :=
  ∀ᵐ t ∂volume.restrict D.I.carrier, ∃ i,
    V.field i (t, D.h t w) ≠ 0 ∧
      Family.wedge (V.field i (t, D.h t w)) (1, deriv (fun s => D.h s w) t) = 0

def uncoveredTrace (V : Family.Foliations) : Set Plane :=
  {c | ∃ x ∈ ball D.base.1 D.radius, ∃ w ∈ ball D.base.2 D.radius,
    c = (x, D.κ (x, w)) ∧ ¬ D.TimeCovered V w}

end ProjectionModel

/-- An actual analytic normal form and its realization in the original
family. This object contains no Nikodym, reuse, or foliation conclusions. -/
structure IntermediateModel {d : ℕ} (G : Family 2 d) where
  data : ProjectionModel d
  j : Fin 2
  F : OpenPartialHomeomorph (ℝ × Aux (d + 1)) (ℝ × Aux (d + 1))
  interval_eq : data.I = G.I
  source_eq : F.source = ball data.base.1 data.radius ×ˢ ball data.base.2 data.radius
  analytic : AnalyticOnNhd ℝ F F.source
  inverse_analytic : AnalyticOnNhd ℝ F.symm F.target
  target_subset : ∀ x ∈ F.target, intermediateCoordinates d j x ∈ G.W
  keep_first : ∀ x, (F x).1 = x.1
  κ_eq : ∀ x, data.κ x = (F x).2 0
  identity : ∀ x ∈ F.source, ∀ t ∈ G.I.carrier,
    G.γ t (intermediateCoordinates d j (F x)) = data.h t x.2

theorem exists_intermediate_model {d : ℕ} (G : Family 2 d) (hW : IsOpen G.W)
    (ha : G.IsAnalytic) (hp : ∀ p ∈ G.W, G.pointRank p = d)
    (hc : ∀ p ∈ G.W, G.curveRank p = d + 1)
    (q : Parameters 2 d) (hq : q ∈ G.W) : Nonempty (IntermediateModel G) := by
  obtain ⟨j, E, hqE, hsW, htW, hEa, hEia, hkeep, hnorm, hid⟩ :=
    corollary_6_3 G hW ha hp hc q hq
  let L := intermediateCoordinates d j
  let b := L.symm q
  let F₀ := (L.toHomeomorph.transOpenPartialHomeomorph E).transHomeomorph L.symm.toHomeomorph
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
  have hFnorm (p : ℝ × Aux (d + 1)) (hp : p ∈ F.source) (he : p.1 = b.1) : F p = p := by
    change L.symm (E (L p)) = p
    rw [hnorm _ (show L p ∈ E.source from hsub hp)]
    · exact L.symm_apply_apply p
    · change p.1 = q.1 j.rev at he
      simpa only [L, intermediateCoordinates_other] using he
  have hFkeep (p : ℝ × Aux (d + 1)) : (F p).1 = p.1 := by
    change (E (L p)).1 j.rev = p.1
    rw [hkeep, intermediateCoordinates_other]
  have hFE (p : ℝ × Aux (d + 1)) : L (F p) = E (L p) := L.apply_symm_apply _
  let h : ℝ → Aux (d + 1) → ℝ := fun t w => G.γ t (L (b.1, w))
  have hline (w : Aux (d + 1)) (hw : w ∈ ball b.2 r) : (b.1, w) ∈ F.source := by
    rw [hs, ← ball_prod_same]
    exact ⟨mem_ball_self hr, hw⟩
  have hWline (w : Aux (d + 1)) (hw : w ∈ ball b.2 r) : L (b.1, w) ∈ G.W :=
    hsW (hsub (hline w hw))
  have hha : AnalyticOnNhd ℝ (fun x : ℝ × Aux (d + 1) => h x.1 x.2)
      (G.I.carrier ×ˢ ball b.2 r) := by
    intro x hx
    exact (ha (x.1, L (b.1, x.2)) ⟨hx.1, hWline _ hx.2⟩).comp
      (f := fun x : ℝ × Aux (d + 1) => (x.1, L (b.1, x.2)))
      (analyticAt_fst.prod ((L.analyticAt _).comp
        (f := fun x : ℝ × Aux (d + 1) => (b.1, x.2)) (analyticAt_const.prod analyticAt_snd)))
  have hident (p : ℝ × Aux (d + 1)) (hp : p ∈ F.source) (t : G.I.carrier) :
      G.γ t (L (F p)) = h t p.2 := by
    rw [hFE]
    have he := hid (L p) (show L p ∈ E.source from hsub hp) t t.property
    rw [intermediateCoordinates_slice] at he
    exact he
  have hhi : ∀ w ∈ ball b.2 r, Injective
      (functionDerivative (fun (t : G.I.carrier) => h t) w) := by
    intro w hw
    let p : ℝ × Aux (d + 1) := (b.1, w)
    have hpF : p ∈ F.source := hline w hw
    let H : (ℝ × Aux (d + 1)) → Parameters 2 d := fun x => L (F x)
    have hHW : H p ∈ G.W := by rw [show H p = E (L p) from hFE p]; exact htW (E.map_source (hsub hpF))
    have hf := fun t : G.I.carrier => (G.parameter_analytic ha _ hHW t).differentiableAt
    have hg : ∀ t : G.I.carrier, DifferentiableAt ℝ (h t) w := by
      intro t
      exact ((hha (t, w) ⟨t.property, hw⟩).comp
        (f := fun w : Aux (d + 1) => ((t : ℝ), w)) (analyticAt_const.prod analyticAt_id)).differentiableAt
    have hFap : AnalyticAt ℝ F p := hFa p (hsub hpF)
    have hFi : AnalyticOnNhd ℝ F.symm F.target := fun x hx => hFia x (htsub hx)
    obtain ⟨A, hA⟩ := chart_fderiv_invertible F (fun x hx => hFa x (hsub hx)) hFi p hpF
    have hsH : Surjective (fderiv ℝ H p) := by
      change Surjective (fderiv ℝ ((L : (ℝ × Aux (d + 1)) → Parameters 2 d) ∘ F) p)
      rw [fderiv_comp p L.differentiableAt hFap.differentiableAt, L.fderiv, ← hA]
      exact L.surjective.comp A.surjective
    have hsP : Surjective (fderiv ℝ (Prod.snd : ℝ × Aux (d + 1) → Aux (d + 1)) p) := by
      rw [hasFDerivAt_snd.fderiv]
      exact fun y => ⟨(0, y), rfl⟩
    have hrange := functionDerivative_range_of_factorization
      (fun (t : G.I.carrier) => G.γ t) (fun (t : G.I.carrier) => h t) H Prod.snd p hf hg
      (L.differentiableAt.comp p hFap.differentiableAt) differentiableAt_snd hsH hsP (by
        intro t
        filter_upwards [F.open_source.mem_nhds hpF] with x hx
        exact hident x hx t)
    apply injective_of_full_range_rank
    rw [← hrange, ← G.curveSpace_eq_range _ hf]
    exact hc _ hHW
  refine ⟨⟨⟨G.I, b, r, hr, h, fun x => (F x).2 0, hha, ?_, ?_, hhi⟩,
    j, F, rfl, ?_, fun x hx => hFa x (hsub hx),
    fun x hx => hFia x (htsub hx), ?_, hFkeep, fun _ => rfl, ?_⟩⟩
  · intro x hx
    have hxF : x ∈ F.source := by rw [hs, ← ball_prod_same]; exact hx
    exact ((ContinuousLinearMap.proj 0 : Aux (d + 1) →L[ℝ] ℝ).analyticAt _).comp
      (analyticAt_snd.comp (hFa x (hsub hxF)))
  · intro w hw
    rw [hFnorm (b.1, w) (hline w hw) rfl]
  · change F.source = ball b.1 r ×ˢ ball b.2 r
    exact hs.trans (ball_prod_same b.1 b.2 r).symm
  · intro x hx
    have hm := htW (show L x ∈ E.target from htsub hx)
    exact hm
  · intro x hx t ht
    exact hident x hx ⟨t, ht⟩

end PlanarNikodym
