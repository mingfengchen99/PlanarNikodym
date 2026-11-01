import PlanarNikodym.Geometry.CenterOrderedStratumLinear

/-! Local analytic centre-preserving coordinates for actual strata at
points where their centre projection has rank two. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace PlanarNikodym

structure CenterOrderedStratumChart (d : ℕ) where
  aux_dim : ℕ
  dim_le : aux_dim ≤ d
  center : Parameters 2 aux_dim
  radius : ℝ
  radius_pos : 0 < radius
  map : Parameters 2 aux_dim → Parameters 2 d
  inverse : Parameters 2 d → Parameters 2 aux_dim
  analytic_map : AnalyticOnNhd ℝ map (closedBall center radius)
  continuous_inverse : ContinuousOn inverse (map '' ball center radius)
  left_inverse : ∀ z ∈ ball center radius, inverse (map z) = z
  keep_center : ∀ z ∈ ball center radius, (map z).1 = z.1
  derivative_injective : ∀ z ∈ ball center radius, Function.Injective (fderiv ℝ map z)

namespace CenterOrderedStratumChart
variable {d : ℕ} (P : CenterOrderedStratumChart d)
def source : Set (Parameters 2 P.aux_dim) := ball P.center P.radius
def image : Set (Parameters 2 d) := P.map '' P.source
theorem open_source : IsOpen P.source := isOpen_ball
theorem bounded_source : Bornology.IsBounded P.source := isBounded_ball
theorem connected_source : IsConnected P.source :=
  (convex_ball P.center P.radius).isConnected (nonempty_ball.mpr P.radius_pos)
end CenterOrderedStratumChart

theorem exists_center_ordered_stratum_chart {d : ℕ}
    (Q : AnalyticStratificationChart (Parameters 2 d))
    (p : Fin Q.dim → ℝ) (hp : p ∈ Q.source)
    (hreg : Function.Surjective (fderiv ℝ (fun u => (Q.map u).1) p)) :
    ∃ P : CenterOrderedStratumChart d,
      P.aux_dim + 2 = Q.dim ∧
      P.map '' closedBall P.center P.radius ⊆ Q.image ∧
      P.image ⊆ Q.image ∧ Q.map p ∈ P.image ∧
      ∀ᶠ y in 𝓝 (Q.map p), y ∈ Q.image → y ∈ P.image := by
  classical
  let L := fderiv ℝ (fun u => (Q.map u).1) p
  obtain ⟨k, e, hdim, hadapt⟩ := exists_center_derivative_coordinates L hreg
  let q₀ := e.symm p
  have heq : e q₀ = p := e.apply_symm_apply p
  let C : (Fin Q.dim → ℝ) → Base 2 := fun u => (Q.map u).1
  let ψ : Parameters 2 k → Parameters 2 k := fun z => (C (e z), z.2)
  have hQa : AnalyticAt ℝ Q.map (e q₀) := by rw [heq]; exact Q.analytic_map p hp
  have hCa : AnalyticAt ℝ C (e q₀) := analyticAt_fst.comp hQa
  have hψ : AnalyticAt ℝ ψ q₀ :=
    (hCa.comp (e.analyticAt q₀)).prod analyticAt_snd
  have hD := (hCa.differentiableAt.hasFDerivAt.comp q₀ e.hasFDerivAt).prodMk
    (hasFDerivAt_snd (𝕜 := ℝ) (p := q₀))
  have hlin : ((fderiv ℝ C (e q₀)).comp e.toContinuousLinearMap).prod
      (ContinuousLinearMap.snd ℝ (Base 2) (Fin k → ℝ)) =
      ContinuousLinearMap.id ℝ (Parameters 2 k) := by
    apply ContinuousLinearMap.ext
    intro z
    apply Prod.ext
    · change fderiv ℝ C (e q₀) (e z) = z.1
      rw [heq]
      exact hadapt z
    · rfl
  have hDψ : HasFDerivAt ψ (ContinuousLinearMap.id ℝ (Parameters 2 k)) q₀ := by
    rw [hlin] at hD
    exact hD
  have hi : (fderiv ℝ ψ q₀).IsInvertible := by
    rw [hDψ.fderiv]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  have hqnear : e ⁻¹' Q.source ∈ 𝓝 q₀ :=
    (Q.open_source.preimage e.continuous).mem_nhds (by simpa only [mem_preimage, heq] using hp)
  obtain ⟨χ, hqχ, hχsub, hχ, hχa, hχia⟩ :=
    exists_analytic_chart ψ q₀ hψ hi (e ⁻¹' Q.source) hqnear
  let c := χ q₀
  have hc : c ∈ χ.target := χ.map_source hqχ
  obtain ⟨r, hr, hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (χ.open_target.mem_nhds hc)
  let g : Parameters 2 k → (Fin Q.dim → ℝ) := fun z => e (χ.symm z)
  let Φ : Parameters 2 k → Parameters 2 d := fun z => Q.map (g z)
  let J : Parameters 2 d → Parameters 2 k := fun y => χ (e.symm (Q.inverse y))
  have hgS {z : Parameters 2 k} (hz : z ∈ closedBall c r) : g z ∈ Q.source :=
    hχsub (χ.map_target (hrsub hz))
  have hgA {z : Parameters 2 k} (hz : z ∈ closedBall c r) : AnalyticAt ℝ g z :=
    (e.analyticAt _).comp (hχia z (hrsub hz))
  have hΦa : AnalyticOnNhd ℝ Φ (closedBall c r) := fun z hz =>
    (Q.analytic_map (g z) (hgS hz)).comp (hgA hz)
  have hΦsub : Φ '' ball c r ⊆ Q.image := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨g z, hgS (ball_subset_closedBall hz), rfl⟩
  have hJleft (z : Parameters 2 k) (hz : z ∈ ball c r) : J (Φ z) = z := by
    change χ (e.symm (Q.inverse (Q.map (e (χ.symm z))))) = z
    rw [Q.left_inverse _ (hgS (ball_subset_closedBall hz)), e.symm_apply_apply,
      χ.right_inv (hrsub (ball_subset_closedBall hz))]
  have hJχ {y : Parameters 2 d} (hy : y ∈ Φ '' ball c r) :
      e.symm (Q.inverse y) ∈ χ.source := by
    obtain ⟨z, hz, rfl⟩ := hy
    change e.symm (Q.inverse (Q.map (g z))) ∈ χ.source
    rw [Q.left_inverse _ (hgS (ball_subset_closedBall hz))]
    simpa only [g, e.symm_apply_apply] using χ.map_target (hrsub (ball_subset_closedBall hz))
  have hJcont : ContinuousOn J (Φ '' ball c r) := by
    intro y hy
    have hQci := (Q.continuous_inverse.mono hΦsub) y hy
    have heci : ContinuousWithinAt (fun x => e.symm (Q.inverse x)) (Φ '' ball c r) y :=
      ContinuousAt.comp_continuousWithinAt (f := Q.inverse) (g := e.symm)
        e.symm.continuous.continuousAt hQci
    exact ContinuousAt.comp_continuousWithinAt (f := fun x => e.symm (Q.inverse x))
      (g := χ) (χ.continuousAt (hJχ hy)) heci
  have hkeep (z : Parameters 2 k) (hz : z ∈ ball c r) : (Φ z).1 = z.1 := by
    have hv := χ.right_inv (hrsub (ball_subset_closedBall hz))
    rw [hχ] at hv
    exact congrArg Prod.fst hv
  have hgi (z : Parameters 2 k) (hz : z ∈ ball c r) :
      Function.Injective (fderiv ℝ g z) := by
    apply AnalyticStratificationChart.fderiv_injective_of_factor isOpen_ball hz g id
      (fun u => χ (e.symm u)) (hgA (ball_subset_closedBall hz)).differentiableAt
    · have hχat : AnalyticAt ℝ χ (e.symm (g z)) := by
        simpa only [g, e.symm_apply_apply] using
          hχa _ (χ.map_target (hrsub (ball_subset_closedBall hz)))
      exact (AnalyticAt.comp (f := e.symm) (g := χ) hχat
        (e.symm.analyticAt (g z))).differentiableAt
    · intro u hu
      change χ (e.symm (e (χ.symm u))) = u
      rw [e.symm_apply_apply]
      exact χ.right_inv (hrsub (ball_subset_closedBall hu))
    · simp only [fderiv_id]
      intro v w hvw
      exact hvw
  have hΦi (z : Parameters 2 k) (hz : z ∈ ball c r) :
      Function.Injective (fderiv ℝ Φ z) := by
    change Function.Injective (fderiv ℝ (Q.map ∘ g) z)
    rw [fderiv_comp z (Q.analytic_map _ (hgS (ball_subset_closedBall hz))).differentiableAt
      (hgA (ball_subset_closedBall hz)).differentiableAt]
    exact (Q.derivative_injective _ (hgS (ball_subset_closedBall hz))).comp (hgi z hz)
  have hk : k ≤ d := by
    have hd := Q.dim_le_finrank
    simp only [Parameters, Base, Aux, Module.finrank_prod, Module.finrank_fin_fun] at hd
    omega
  let P : CenterOrderedStratumChart d :=
    { aux_dim := k
      dim_le := hk
      center := c
      radius := r
      radius_pos := hr
      map := Φ
      inverse := J
      analytic_map := hΦa
      continuous_inverse := hJcont
      left_inverse := hJleft
      keep_center := hkeep
      derivative_injective := hΦi }
  refine ⟨P, hdim, ?_, hΦsub, ?_, ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    exact ⟨g z, hgS hz, rfl⟩
  · refine ⟨c, mem_ball_self hr, ?_⟩
    change Q.map (e (χ.symm (χ q₀))) = Q.map p
    rw [χ.left_inv hqχ, heq]
  · have hy₀ : Q.map p ∈ Q.image := ⟨p, hp, rfl⟩
    have hQci := Q.continuous_inverse (Q.map p) hy₀
    have heci : ContinuousWithinAt (fun y => e.symm (Q.inverse y)) Q.image (Q.map p) :=
      ContinuousAt.comp_continuousWithinAt (f := Q.inverse) (g := e.symm)
        e.symm.continuous.continuousAt hQci
    have heT : Tendsto (fun y => e.symm (Q.inverse y))
        (𝓝[Q.image] (Q.map p)) (𝓝 q₀) := by
      change Tendsto (fun y => e.symm (Q.inverse y))
        (𝓝[Q.image] (Q.map p)) (𝓝 (e.symm (Q.inverse (Q.map p)))) at heci
      simpa only [Q.left_inverse p hp] using heci
    have hsrc := heT.eventually (χ.open_source.mem_nhds hqχ)
    have hJt := (χ.continuousAt hqχ).tendsto.comp heT
    have hball := hJt.eventually (isOpen_ball.mem_nhds (mem_ball_self hr))
    have hnear := eventually_nhdsWithin_iff.mp (hsrc.and hball)
    filter_upwards [hnear] with y hy hyQ
    obtain ⟨hys, hyb⟩ := hy hyQ
    refine ⟨J y, hyb, ?_⟩
    change Q.map (e (χ.symm (χ (e.symm (Q.inverse y))))) = y
    rw [χ.left_inv hys, e.apply_symm_apply, Q.map_inverse hyQ]

end PlanarNikodym
