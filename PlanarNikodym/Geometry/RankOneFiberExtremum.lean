import PlanarNikodym.Geometry.AnalyticRegularLevelChart
import PlanarNikodym.Geometry.PlanarCriticalLinearAlgebra
import PlanarNikodym.Geometry.AnalyticCriticalValues

/-! Fermat's theorem on the fibers of an actual analytic planar map of
constant rank one. A regular scalar level is constructed; the remaining
center coordinate is proved constant on it by the mean value theorem. -/
noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym

theorem planar_nonsurjective_kernel_coordinate {n : ℕ}
    (L : (Fin n → ℝ) →L[ℝ] (Fin 2 → ℝ)) (hL : ¬ Function.Surjective L)
    (j : Fin 2) (hn : ∃ w, L w j ≠ 0) {v : Fin n → ℝ} (hv : L v j = 0) :
    L v = 0 := by
  obtain ⟨w, hw⟩ := hn
  have hd := (planar_not_surjective_iff_minors_zero L).mp hL v w
  ext i
  fin_cases j <;> fin_cases i
  · exact hv
  · change L v 0 = 0 at hv
    change L w 0 ≠ 0 at hw
    change L v 1 = 0
    rw [hv, zero_mul, zero_sub, neg_eq_zero] at hd
    exact (mul_eq_zero.mp hd).resolve_right hw
  · change L v 1 = 0 at hv
    change L w 1 ≠ 0 at hw
    change L v 0 = 0
    rw [hv, zero_mul, sub_zero] at hd
    exact (mul_eq_zero.mp hd).resolve_right hw
  · exact hv

theorem analytic_rank_one_fiber_maximum_derivative
    {n : ℕ} (C : (Fin n → ℝ) → (Fin 2 → ℝ))
    (g : (Fin n → ℝ) → ℝ) {U : Set (Fin n → ℝ)}
    (ho : IsOpen U) (ha : AnalyticOnNhd ℝ C U) (hg : AnalyticOnNhd ℝ g U)
    (hr : ∀ z ∈ U, ¬ Function.Surjective (fderiv ℝ C z))
    {x : Fin n → ℝ} (hx : x ∈ U) (hn : fderiv ℝ C x ≠ 0)
    (hm : IsMaxOn g {z | z ∈ U ∧ C z = C x} x)
    {v : Fin n → ℝ} (hv : fderiv ℝ C x v = 0) : fderiv ℝ g x v = 0 := by
  classical
  cases n with
  | zero =>
    have he : v = 0 := Subsingleton.elim _ _
    simp only [he, map_zero]
  | succ n =>
    obtain ⟨w, hw⟩ : ∃ w, fderiv ℝ C x w ≠ 0 := by
      by_contra! h
      exact hn (ContinuousLinearMap.ext h)
    obtain ⟨j, hj⟩ : ∃ j : Fin 2, fderiv ℝ C x w j ≠ 0 := by
      by_contra! h
      exact hw (funext h)
    let f : (Fin (n + 1) → ℝ) → ℝ := fun z => C z j
    have hfa : AnalyticOnNhd ℝ f U := fun z hz =>
      ((ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ).analyticAt _).comp (ha z hz)
    have hfd (z : Fin (n + 1) → ℝ) (hz : z ∈ U) :
        fderiv ℝ f z = (ContinuousLinearMap.proj j).comp (fderiv ℝ C z) :=
      ((ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp z
        (ha z hz).differentiableAt.hasFDerivAt).fderiv
    have hfn : fderiv ℝ f x ≠ 0 := by
      intro he
      apply hj
      have hew := congrArg (fun D : (Fin (n + 1) → ℝ) →L[ℝ] ℝ => D w) he
      rwa [hfd x hx] at hew
    obtain ⟨k, hk⟩ := exists_coordinate_derivative_ne_zero (fderiv ℝ f x) hfn
    obtain ⟨P, q, _, hq, hqx, hPU, hPf, hT⟩ :=
      exists_analytic_regular_level_chart f ho hfa hx k hk
    have hCa : AnalyticOnNhd ℝ (C ∘ P.map) P.source :=
      fun z hz => (ha _ (hPU (mem_image_of_mem _ hz))).comp (P.analytic_map z hz)
    have hCzero : ∀ z ∈ P.source, fderiv ℝ (C ∘ P.map) z = 0 := by
      intro z hz
      have hzU := hPU (mem_image_of_mem _ hz)
      have hflat : f ∘ P.map =ᶠ[𝓝 z] fun _ => f x := by
        filter_upwards [P.open_source.mem_nhds hz] with u hu
        exact (hPf _ (mem_image_of_mem _ hu)).1
      have hflatD := hflat.fderiv_eq (𝕜 := ℝ)
      rw [fderiv_comp z (hfa _ hzU).differentiableAt (P.analytic_map z hz).differentiableAt,
        fderiv_const_apply] at hflatD
      rw [fderiv_comp z (ha _ hzU).differentiableAt (P.analytic_map z hz).differentiableAt]
      ext u i
      have hnC : ∃ w, fderiv ℝ C (P.map z) w j ≠ 0 := by
        refine ⟨Pi.single k 1, ?_⟩
        have hne := (hPf _ (mem_image_of_mem _ hz)).2
        rwa [hfd _ hzU] at hne
      have hker : fderiv ℝ C (P.map z) (fderiv ℝ P.map z u) j = 0 := by
        have he := congrArg (fun D : (Fin P.dim → ℝ) →L[ℝ] ℝ => D u) hflatD
        rwa [hfd _ hzU] at he
      exact congrFun (planar_nonsurjective_kernel_coordinate _ (hr _ hzU) j hnC hker) i
    have hCconst (z : Fin P.dim → ℝ) (hz : z ∈ P.source) : C (P.map z) = C x := by
      have he := P.open_source.is_const_of_fderiv_eq_zero P.connected_source.isPreconnected
        hCa.differentiableOn hCzero hz hq
      simpa only [Function.comp_apply, hqx] using he
    have hgm : IsMaxOn (g ∘ P.map) P.source q := by
      intro z hz
      change g (P.map z) ≤ g (P.map q)
      rw [hqx]
      exact hm ⟨hPU (mem_image_of_mem _ hz), hCconst z hz⟩
    have hgz := (hgm.isLocalMax (P.open_source.mem_nhds hq)).fderiv_eq_zero
    rw [fderiv_comp q (hg _ (hPU (mem_image_of_mem _ hq))).differentiableAt
      (P.analytic_map q hq).differentiableAt, hqx] at hgz
    have hvf : v ∈ (fderiv ℝ f x).toLinearMap.ker := by
      change fderiv ℝ f x v = 0
      rw [hfd x hx]
      change fderiv ℝ C x v j = 0
      rw [hv]
      rfl
    obtain ⟨u, hu⟩ := (hT ▸ hvf : v ∈ (fderiv ℝ P.map q).toLinearMap.range)
    have he := congrArg (fun D : (Fin P.dim → ℝ) →L[ℝ] ℝ => D u) hgz
    change fderiv ℝ P.map q u = v at hu
    change fderiv ℝ g x (fderiv ℝ P.map q u) = 0 at he
    rwa [hu] at he

end PlanarNikodym
