import PlanarNikodym.Projection.ThinRectangleProjection

/-! Uniform transverse direction cones for nonlinear segment replacement.

Distinct regular projective slopes produce actual closed parameter boxes
and a direction interval on which the covering family's signed directional
derivative has a positive uniform lower bound. The derivative norm also has
a finite uniform upper bound. These bounds are constructed from continuity.
-/

noncomputable section
open Set Filter Metric
open scoped Topology

namespace PlanarNikodym

/-- A nonzero derivative in one direction persists on a product of a closed
spatial-parameter box and a closed interval of projective directions. -/
theorem exists_uniform_scalar_transverse_cone
    {ψ : ℝ × Plane → ℝ} {U : Set (ℝ × Plane)}
    (hU : IsOpen U) {p : ℝ × Plane} (hp : p ∈ U)
    (hψ : AnalyticAt ℝ ψ p) (hh : scalarHeadDerivative ψ p ≠ 0)
    (s₀ : ℝ) (hd : fderiv ℝ ψ p (0, (-s₀, 1)) ≠ 0) :
    ∃ r > 0, ∃ ρ > 0, ∃ m > 0, ∃ M > 0, ∃ σ : ℝ,
      (σ = 1 ∨ σ = -1) ∧
      closedBall p r ⊆ U ∧
      (∀ z ∈ closedBall p r, AnalyticAt ℝ ψ z ∧
        scalarHeadDerivative ψ z ≠ 0 ∧ ‖fderiv ℝ ψ z‖ ≤ M) ∧
      ∀ z ∈ closedBall p r, ∀ s ∈ closedBall s₀ ρ,
        m ≤ σ * fderiv ℝ ψ z (0, (-s, 1)) := by
  obtain ⟨σ, hσ, hsign⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      0 < σ * fderiv ℝ ψ p (0, (-s₀, 1)) := by
    rcases lt_or_gt_of_ne hd with hn | hp
    · exact ⟨-1, Or.inr rfl, by linarith⟩
    · exact ⟨1, Or.inl rfl, by simpa using hp⟩
  let g : (ℝ × Plane) × ℝ → ℝ :=
    fun z => σ * fderiv ℝ ψ z.1 (0, (-z.2, 1))
  let m := g (p, s₀) / 2
  have hm : 0 < m := half_pos hsign
  have hg : ContinuousAt g (p, s₀) := by
    apply continuousAt_const.mul
    exact (hψ.fderiv.continuousAt.comp continuousAt_fst).clm_apply (by fun_prop)
  have hgood : ∀ᶠ z in 𝓝 (p, s₀), m < g z :=
    hg.preimage_mem_nhds (isOpen_Ioi.mem_nhds (half_lt_self hsign))
  obtain ⟨c, hc, hcb⟩ := Metric.mem_nhds_iff.mp hgood
  let M := ‖fderiv ℝ ψ p‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hMbase : ‖fderiv ℝ ψ p‖ < M := by dsimp [M]; linarith
  have hnorm : ∀ᶠ z in 𝓝 p, ‖fderiv ℝ ψ z‖ < M :=
    hψ.fderiv.continuousAt.norm.preimage_mem_nhds
      (isOpen_Iio.mem_nhds hMbase)
  have hregular : ∀ᶠ z in 𝓝 p, z ∈ U ∧ AnalyticAt ℝ ψ z ∧
      scalarHeadDerivative ψ z ≠ 0 ∧ ‖fderiv ℝ ψ z‖ < M := by
    filter_upwards [hU.mem_nhds hp, hψ.eventually_analyticAt,
      (scalarHeadDerivative_analyticAt hψ).continuousAt.eventually_ne hh, hnorm]
      with z hz han hhead hb
    exact ⟨hz, han, hhead, hb⟩
  obtain ⟨b, hb, hbb⟩ := Metric.mem_nhds_iff.mp hregular
  let r := min (b / 2) (c / 2)
  let ρ := c / 2
  have hr : 0 < r := lt_min (half_pos hb) (half_pos hc)
  have hρ : 0 < ρ := half_pos hc
  have hrb : r < b := (min_le_left _ _).trans_lt (half_lt_self hb)
  have hrc : r ≤ c / 2 := min_le_right _ _
  have hreg (z : ℝ × Plane) (hz : z ∈ closedBall p r) :
      z ∈ U ∧ AnalyticAt ℝ ψ z ∧ scalarHeadDerivative ψ z ≠ 0 ∧
        ‖fderiv ℝ ψ z‖ < M :=
    hbb (closedBall_subset_ball hrb hz)
  refine ⟨r, hr, ρ, hρ, m, hm, M, hM, σ, hσ,
    fun z hz => (hreg z hz).1,
    fun z hz => ⟨(hreg z hz).2.1, (hreg z hz).2.2.1, (hreg z hz).2.2.2.le⟩, ?_⟩
  intro z hz s hs
  have hpairs : (z, s) ∈ closedBall (p, s₀) (c / 2) := by
    rw [← closedBall_prod_same]
    exact ⟨closedBall_subset_closedBall hrc hz, hs⟩
  exact (hcb (closedBall_subset_ball (half_lt_self hc) hpairs)).le

/-- Two distinct regular slopes yield a common closed parameter radius and
a genuine uniform transverse cone for the covering family. No monotonicity
or projection-selection input is required for this local consequence. -/
theorem exists_separated_scalar_uniform_transverse_cone
    {φ ψ : ℝ × Plane → ℝ} {U V : Set (ℝ × Plane)}
    (hU : IsOpen U) (hV : IsOpen V) (t x : ℝ) (q : Plane)
    (htq : (t, q) ∈ U) (hxq : (x, q) ∈ V)
    (hφ : AnalyticAt ℝ φ (t, q)) (hψ : AnalyticAt ℝ ψ (x, q))
    (hhφ : scalarHeadDerivative φ (t, q) ≠ 0)
    (hhψ : scalarHeadDerivative ψ (x, q) ≠ 0)
    (hne : scalarGradientSlope φ (t, q) ≠ scalarGradientSlope ψ (x, q)) :
    ∃ r > 0, ∃ ρ > 0, ∃ m > 0, ∃ M > 0, ∃ σ : ℝ,
      (σ = 1 ∨ σ = -1) ∧
      closedBall (t, q) r ⊆ U ∧ closedBall (x, q) r ⊆ V ∧
      (∀ z ∈ closedBall (t, q) r, AnalyticAt ℝ φ z ∧
        scalarHeadDerivative φ z ≠ 0 ∧
        scalarGradientSlope φ z ∈ closedBall (scalarGradientSlope φ (t, q)) ρ) ∧
      (∀ z ∈ closedBall (x, q) r, AnalyticAt ℝ ψ z ∧
        scalarHeadDerivative ψ z ≠ 0 ∧ ‖fderiv ℝ ψ z‖ ≤ M) ∧
      ∀ z ∈ closedBall (x, q) r,
        ∀ s ∈ closedBall (scalarGradientSlope φ (t, q)) ρ,
          m ≤ σ * fderiv ℝ ψ z (0, (-s, 1)) := by
  have hd : fderiv ℝ ψ (x, q) (0, (-scalarGradientSlope φ (t, q), 1)) ≠ 0 := by
    rw [scalar_fderiv_slopeDirection hhψ]
    exact mul_ne_zero hhψ (sub_ne_zero.mpr hne.symm)
  obtain ⟨b, hb, ρ, hρ, m, hm, M, hM, σ, hσ, hVb, hψb, hcone⟩ :=
    exists_uniform_scalar_transverse_cone hV hxq hψ hhψ
      (scalarGradientSlope φ (t, q)) hd
  have hslope : ∀ᶠ z in 𝓝 (t, q),
      scalarGradientSlope φ z ∈ ball (scalarGradientSlope φ (t, q)) ρ :=
    (scalarGradientSlope_analyticAt hφ hhφ).continuousAt.preimage_mem_nhds
      (ball_mem_nhds _ hρ)
  have hregular : ∀ᶠ z in 𝓝 (t, q), z ∈ U ∧ AnalyticAt ℝ φ z ∧
      scalarHeadDerivative φ z ≠ 0 ∧
        scalarGradientSlope φ z ∈ ball (scalarGradientSlope φ (t, q)) ρ := by
    filter_upwards [hU.mem_nhds htq, hφ.eventually_analyticAt,
      (scalarHeadDerivative_analyticAt hφ).continuousAt.eventually_ne hhφ, hslope]
      with z hz ha hh hs
    exact ⟨hz, ha, hh, hs⟩
  obtain ⟨a, ha, hab⟩ := Metric.mem_nhds_iff.mp hregular
  let r := min (a / 2) b
  have hr : 0 < r := lt_min (half_pos ha) hb
  have hra : r < a := (min_le_left _ _).trans_lt (half_lt_self ha)
  have hrb : r ≤ b := min_le_right _ _
  have hφr (z : ℝ × Plane) (hz : z ∈ closedBall (t, q) r) :
      z ∈ U ∧ AnalyticAt ℝ φ z ∧ scalarHeadDerivative φ z ≠ 0 ∧
        scalarGradientSlope φ z ∈ closedBall (scalarGradientSlope φ (t, q)) ρ := by
    obtain ⟨hzU, hza, hzh, hzs⟩ := hab (closedBall_subset_ball hra hz)
    exact ⟨hzU, hza, hzh, ball_subset_closedBall hzs⟩
  refine ⟨r, hr, ρ, hρ, m, hm, M, hM, σ, hσ,
    fun z hz => (hφr z hz).1, (closedBall_subset_closedBall hrb).trans hVb,
    fun z hz => (hφr z hz).2, ?_, ?_⟩
  · exact fun z hz => hψb z (closedBall_subset_closedBall hrb hz)
  · exact fun z hz => hcone z (closedBall_subset_closedBall hrb hz)

/-- The signed spatial derivative used by finite covering replacements is
the restriction of the actual ambient derivative to spatial directions. -/
theorem signed_scalarSlice_fderiv_apply
    {ψ : ℝ × Plane → ℝ} {p : ℝ × Plane}
    (hψ : DifferentiableAt ℝ ψ p) (σ : ℝ) (v : Plane) :
    fderiv ℝ (fun q : Plane => σ * ψ (p.1, q)) p.2 v =
      σ * fderiv ℝ ψ p (0, v) := by
  have hs : DifferentiableAt ℝ (fun q : Plane => ψ (p.1, q)) p.2 :=
    hψ.comp p.2 (by fun_prop)
  rw [fderiv_const_mul hs, fderiv_snd_slice ψ p hψ]
  rfl

/-- Choosing the sign to make the cone positive does not enlarge the
derivative norm. Spatial restriction has operator norm at most one. -/
theorem norm_signed_scalarSlice_fderiv_le
    {ψ : ℝ × Plane → ℝ} {p : ℝ × Plane} {σ : ℝ}
    (hψ : DifferentiableAt ℝ ψ p) (hσ : σ = 1 ∨ σ = -1) :
    ‖fderiv ℝ (fun q : Plane => σ * ψ (p.1, q)) p.2‖ ≤ ‖fderiv ℝ ψ p‖ := by
  have hs : DifferentiableAt ℝ (fun q : Plane => ψ (p.1, q)) p.2 :=
    hψ.comp p.2 (by fun_prop)
  have hσnorm : ‖σ‖ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  rw [fderiv_const_mul hs, norm_smul, hσnorm, one_mul, fderiv_snd_slice ψ p hψ]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  simpa using mul_le_mul_of_nonneg_left
    (ContinuousLinearMap.norm_inr_le_one (𝕜 := ℝ) (E := ℝ) (F := Plane))
    (norm_nonneg (fderiv ℝ ψ p))

end PlanarNikodym
