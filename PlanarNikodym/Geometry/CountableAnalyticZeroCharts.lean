import PlanarNikodym.Cells.CountableAuxiliaryCharts
import PlanarNikodym.Geometry.AnalyticFiniteOrder

/-! Actual dimension-dropping parametrizations of analytic zero sets.
The parametrizations are allowed to cover a higher derivative zero layer;
they are not asserted to be open in, or contained in, the original zero set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace PlanarNikodym

/-- A genuine analytic parametrization with strictly smaller source dimension. -/
structure AnalyticDimensionDropChart (n : ℕ) (U : Set (Aux n)) where
  dim : ℕ
  dim_lt : dim < n
  source : Set (Aux dim)
  open_source : IsOpen source
  map : Aux dim → Aux n
  analytic_map : AnalyticOnNhd ℝ map source
  maps_to : MapsTo map source U

/-- Regular level charts lie in the original zero set, unlike the higher-jet
charts used later for singular zeros. -/
theorem exists_countable_regular_analytic_zero_charts {n : ℕ}
    (f : Aux (n + 1) → ℝ) {U : Set (Aux (n + 1))}
    (ho : IsOpen U) (ha : AnalyticOnNhd ℝ f U) (j : Fin (n + 1)) :
    ∃ C : Set (AnalyticDimensionDropChart (n + 1) U), C.Countable ∧
      (∀ Q ∈ C, Q.dim = n ∧ ∀ v ∈ Q.source, f (Q.map v) = 0) ∧
      ∀ x ∈ U, f x = 0 → fderiv ℝ f x (Pi.single j 1) ≠ 0 →
        ∃ Q ∈ C, ∃ v ∈ Q.source, Q.map v = x := by
  classical
  let G : Family 2 (n + 1) :=
    { I := ⟨0, 1, by norm_num⟩
      W := Set.univ ×ˢ U
      γ := fun _ _ => 0 }
  have hGo : IsOpen G.W := isOpen_univ.prod ho
  have hGa : G.IsAnalytic := fun _ _ => analyticAt_const
  have hfa : AnalyticOnNhd ℝ (fun p : Parameters 2 (n + 1) => f p.2) G.W :=
    fun p hp => (ha p.2 hp.2).comp analyticAt_snd
  obtain ⟨S, hSc, hS, hcover⟩ :=
    exists_countable_regular_auxiliary_zero_pieces G hGo hGa
      (fun p => f p.2) hfa j
  let Q (P : S) : AnalyticDimensionDropChart (n + 1) U :=
    { dim := P.1.dim
      dim_lt := by rw [(hS P.1 P.2).1]; omega
      source := (fun v => ((0 : Base 2), v)) ⁻¹' P.1.family.W
      open_source := P.1.open_domain.preimage (continuous_const.prodMk continuous_id)
      map := fun v => (P.1.embed (0, v)).2
      analytic_map := fun v hv =>
        analyticAt_snd.comp ((P.1.analytic_embed (0, v) hv).comp
          (analyticAt_const.prod analyticAt_id))
      maps_to := fun v hv => (P.1.maps_to (0, v) hv).2 }
  haveI : Countable S := hSc.to_subtype
  refine ⟨Set.range Q, Set.countable_range Q, ?_, ?_⟩
  · rintro _ ⟨P, rfl⟩
    refine ⟨(hS P.1 P.2).1, ?_⟩
    intro v hv
    exact (hS P.1 P.2).2.2 (mem_image_of_mem P.1.embed hv)
  · intro x hx hz hj
    have hj' : fderiv ℝ (fun p : Parameters 2 (n + 1) => f p.2)
        (0, x) (0, Pi.single j 1) ≠ 0 := by
      change fderiv ℝ (f ∘ Prod.snd) (0, x) (0, Pi.single j 1) ≠ 0
      rw [fderiv_comp (0, x) (ha x hx).differentiableAt differentiableAt_snd,
        fderiv_snd]
      exact hj
    obtain ⟨P, hP, q, hq, he⟩ :=
      hcover (0, x) ⟨Set.mem_univ _, hx⟩ hz hj'
    have hq0 : q.1 = 0 :=
      (P.keep_center q hq).symm.trans (congrArg Prod.fst he)
    have hqeq : q = (0, q.2) := Prod.ext hq0 rfl
    refine ⟨Q ⟨P, hP⟩, Set.mem_range_self _, q.2, ?_, ?_⟩
    · change (0, q.2) ∈ P.family.W
      exact hqeq ▸ hq
    · change (P.embed (0, q.2)).2 = x
      rw [← hqeq]
      exact congrArg Prod.snd he

theorem exists_countable_nonflat_analytic_zero_charts {n : ℕ}
    (f : Aux (n + 1) → ℝ) {U : Set (Aux (n + 1))}
    (ho : IsOpen U) (ha : AnalyticOnNhd ℝ f U) :
    ∃ C : Set (AnalyticDimensionDropChart (n + 1) U), C.Countable ∧
      (∀ Q ∈ C, Q.dim = n) ∧
      ∀ x ∈ U, f x = 0 → (¬ ∀ᶠ y in 𝓝 x, f y = 0) →
        ∃ Q ∈ C, ∃ v ∈ Q.source, Q.map v = x := by
  classical
  let G : Family 2 (n + 1) :=
    { I := ⟨0, 1, by norm_num⟩
      W := Set.univ ×ˢ U
      γ := fun _ _ => 0 }
  have hGo : IsOpen G.W := isOpen_univ.prod ho
  have hGa : G.IsAnalytic := fun _ _ => analyticAt_const
  have hfa : AnalyticOnNhd ℝ (fun p : Parameters 2 (n + 1) => f p.2) G.W :=
    fun p hp => (ha p.2 hp.2).comp analyticAt_snd
  obtain ⟨S, hSc, hS, hcover⟩ :=
    exists_countable_nonflat_auxiliary_zero_pieces G hGo hGa
      (fun p => f p.2) hfa
  let Q (P : S) : AnalyticDimensionDropChart (n + 1) U :=
    { dim := P.1.dim
      dim_lt := by rw [(hS P.1 P.2).1]; omega
      source := (fun v => ((0 : Base 2), v)) ⁻¹' P.1.family.W
      open_source := P.1.open_domain.preimage (continuous_const.prodMk continuous_id)
      map := fun v => (P.1.embed (0, v)).2
      analytic_map := fun v hv =>
        analyticAt_snd.comp ((P.1.analytic_embed (0, v) hv).comp
          (analyticAt_const.prod analyticAt_id))
      maps_to := fun v hv => (P.1.maps_to (0, v) hv).2 }
  haveI : Countable S := hSc.to_subtype
  refine ⟨Set.range Q, Set.countable_range Q, ?_, ?_⟩
  · rintro _ ⟨P, rfl⟩
    exact (hS P.1 P.2).1
  · intro x hx hz hn
    obtain ⟨P, hP, q, hq, he⟩ :=
      hcover (0, x) ⟨Set.mem_univ _, hx⟩ hz hn
    have hq0 : q.1 = 0 :=
      (P.keep_center q hq).symm.trans (congrArg Prod.fst he)
    have hqeq : q = (0, q.2) := Prod.ext hq0 rfl
    refine ⟨Q ⟨P, hP⟩, Set.mem_range_self _, q.2, ?_, ?_⟩
    · change (0, q.2) ∈ P.family.W
      exact hqeq ▸ hq
    · change (P.embed (0, q.2)).2 = x
      rw [← hqeq]
      exact congrArg Prod.snd he

/-- On a connected domain a nontrivial analytic function has no flat germ,
so the preceding genuine countable parametrizations cover every zero. -/
theorem exists_countable_analytic_zero_charts {n : ℕ}
    (f : Aux (n + 1) → ℝ) {U : Set (Aux (n + 1))}
    (ho : IsOpen U) (ha : AnalyticOnNhd ℝ f U) (hc : IsPreconnected U)
    (hne : ∃ x ∈ U, f x ≠ 0) :
    ∃ C : Set (AnalyticDimensionDropChart (n + 1) U), C.Countable ∧
      (∀ Q ∈ C, Q.dim = n) ∧
      ∀ x ∈ U, f x = 0 → ∃ Q ∈ C, ∃ v ∈ Q.source, Q.map v = x := by
  obtain ⟨C, hC, hdim, hcover⟩ :=
    exists_countable_nonflat_analytic_zero_charts f ho ha
  refine ⟨C, hC, hdim, fun x hx hz => hcover x hx hz ?_⟩
  intro hflat
  have he := ha.eqOn_of_preconnected_of_eventuallyEq (fun _ _ => analyticAt_const)
    hc hx hflat
  obtain ⟨y, hy, hny⟩ := hne
  exact hny (he hy)

end PlanarNikodym
