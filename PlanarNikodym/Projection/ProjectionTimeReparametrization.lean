import PlanarNikodym.Projection.ProjectionAngleCoordinates

/-! Affine time coordinates for separated projection families.

Each original interval is transported to a chosen unit interval `[c,c+1]`.
The sign reverses decreasing angle slices, so both projection families
can be placed on ordered, disjoint intervals with increasing angles.
These are actual changes of variables of the projection functions.
-/

noncomputable section
open Set Filter Metric
open scoped Topology

namespace PlanarNikodym

/-- Affine time map from a unit interval to a radius-`r` interval around
`t`. A sign of `-1` reverses its orientation. -/
def projectionAffineTime (t r σ c u : ℝ) : ℝ :=
  t + σ * r * (2 * (u - c) - 1)

theorem projectionAffineTime_analyticAt (t r σ c u : ℝ) :
    AnalyticAt ℝ (projectionAffineTime t r σ c) u := by
  unfold projectionAffineTime
  exact analyticAt_const.add
    (analyticAt_const.mul
      ((analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).sub analyticAt_const))

theorem projectionAffineTime_hasDerivAt (t r σ c u : ℝ) :
    HasDerivAt (projectionAffineTime t r σ c) (2 * σ * r) u := by
  change HasDerivAt (fun x => t + σ * r * (2 * (x - c) - 1)) (2 * σ * r) u
  simpa only [id_eq, mul_one, one_mul, mul_assoc, mul_comm,
    mul_left_comm] using
    (((((hasDerivAt_id u).sub_const c).const_mul 2).sub_const 1).const_mul
      (σ * r)).const_add t

theorem projectionAffineTime_deriv (t r σ c u : ℝ) :
    deriv (projectionAffineTime t r σ c) u = 2 * σ * r :=
  (projectionAffineTime_hasDerivAt t r σ c u).deriv

theorem projectionAffineTime_mem_closedBall
    (t r σ c u : ℝ) (hr : 0 ≤ r) (hσ : σ = 1 ∨ σ = -1)
    (hu : u ∈ Icc c (c + 1)) :
    projectionAffineTime t r σ c u ∈ closedBall t r := by
  rw [Real.closedBall_eq_Icc]
  rcases hσ with rfl | rfl <;>
    dsimp [projectionAffineTime] <;> constructor <;> nlinarith [hu.1, hu.2]

theorem projectionAffineTime_mem_ball
    (t r σ c u : ℝ) (hr : 0 < r) (hσ : σ = 1 ∨ σ = -1)
    (hu : u ∈ Ioo c (c + 1)) :
    projectionAffineTime t r σ c u ∈ ball t r := by
  rw [Real.ball_eq_Ioo]
  rcases hσ with rfl | rfl <;>
    dsimp [projectionAffineTime] <;> constructor <;> nlinarith [hu.1, hu.2]

/-- Reparametrizing time preserves the source parameter of each
projection. -/
def reparametrizeScalarProjection (ψ : ℝ × Plane → ℝ)
    (t r σ c : ℝ) (p : ℝ × Plane) : ℝ :=
  ψ (projectionAffineTime t r σ c p.1, p.2)

theorem reparametrizeScalarProjection_analyticAt
    {ψ : ℝ × Plane → ℝ} (t r σ c : ℝ) (p : ℝ × Plane)
    (hψ : AnalyticAt ℝ ψ (projectionAffineTime t r σ c p.1, p.2)) :
    AnalyticAt ℝ (reparametrizeScalarProjection ψ t r σ c) p := by
  exact hψ.comp (f := fun z : ℝ × Plane => (projectionAffineTime t r σ c z.1, z.2))
    (((projectionAffineTime_analyticAt t r σ c p.1).comp analyticAt_fst).prod
      analyticAt_snd)

/-- Changing time leaves both components of the actual parameter
gradient unchanged. -/
theorem reparametrizeScalarProjection_parameterDerivatives
    {ψ : ℝ × Plane → ℝ} (t r σ c : ℝ) (p : ℝ × Plane)
    (hψ : AnalyticAt ℝ ψ (projectionAffineTime t r σ c p.1, p.2)) :
    scalarHeadDerivative (reparametrizeScalarProjection ψ t r σ c) p =
        scalarHeadDerivative ψ (projectionAffineTime t r σ c p.1, p.2) ∧
      scalarTailDerivative (reparametrizeScalarProjection ψ t r σ c) p =
        scalarTailDerivative ψ (projectionAffineTime t r σ c p.1, p.2) := by
  have hnew := (reparametrizeScalarProjection_analyticAt t r σ c p hψ).differentiableAt
  have hslice :
      (fderiv ℝ (reparametrizeScalarProjection ψ t r σ c) p).comp
          (ContinuousLinearMap.inr ℝ ℝ Plane) =
        (fderiv ℝ ψ (projectionAffineTime t r σ c p.1, p.2)).comp
          (ContinuousLinearMap.inr ℝ ℝ Plane) := by
    rw [← fderiv_snd_slice _ _ hnew, ← fderiv_snd_slice _ _ hψ.differentiableAt]
    rfl
  exact ⟨congrArg (fun L : Plane →L[ℝ] ℝ => L (1, 0)) hslice,
    congrArg (fun L : Plane →L[ℝ] ℝ => L (0, 1)) hslice⟩

theorem reparametrizeScalarProjection_angle
    {ψ : ℝ × Plane → ℝ} (t r σ c : ℝ) (p : ℝ × Plane)
    (hψ : AnalyticAt ℝ ψ (projectionAffineTime t r σ c p.1, p.2)) :
    scalarGradientAngle (reparametrizeScalarProjection ψ t r σ c) p =
      scalarGradientAngle ψ (projectionAffineTime t r σ c p.1, p.2) := by
  obtain ⟨hh, ht⟩ := reparametrizeScalarProjection_parameterDerivatives t r σ c p hψ
  simp only [scalarGradientAngle, scalarGradientSlope, hh, ht]

/-- Chain rule for the actual affine time map. -/
theorem deriv_comp_projectionAffineTime {f : ℝ → ℝ}
    (t r σ c u : ℝ) (hf : DifferentiableAt ℝ f (projectionAffineTime t r σ c u)) :
    deriv (fun v => f (projectionAffineTime t r σ c v)) u =
      (2 * σ * r) * deriv f (projectionAffineTime t r σ c u) := by
  simpa only [mul_comm, Function.comp_def] using
    (hf.hasDerivAt.comp u (projectionAffineTime_hasDerivAt t r σ c u)).deriv

/-- The angle of the reparametrized function agrees with the composed
angle on a neighbourhood, so their actual time derivatives agree. -/
theorem reparametrizeScalarProjection_angle_deriv
    {ψ : ℝ × Plane → ℝ} (t r σ c u : ℝ) (q : Plane)
    (hψ : AnalyticAt ℝ ψ (projectionAffineTime t r σ c u, q)) :
    deriv (fun v => scalarGradientAngle (reparametrizeScalarProjection ψ t r σ c)
      (v, q)) u =
      deriv (fun v => scalarGradientAngle ψ (projectionAffineTime t r σ c v, q)) u := by
  have hc : ContinuousAt (fun v => (projectionAffineTime t r σ c v, q)) u :=
    (projectionAffineTime_analyticAt t r σ c u).continuousAt.prodMk continuousAt_const
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hc.eventually hψ.eventually_analyticAt] with v hv
  exact reparametrizeScalarProjection_angle t r σ c (v, q) hv

/-- Affine reversal turns uniformly oriented original angle slices into
increasing slices on the chosen closed unit interval. -/
theorem scalarGradientAngle_strictMonoOn_affineTime
    {ψ : ℝ × Plane → ℝ} (t r σ c : ℝ) (q : Plane)
    (hr : 0 < r) (hσ : σ = 1 ∨ σ = -1)
    (hm : StrictMonoOn (fun s => σ * scalarGradientAngle ψ (s, q)) (closedBall t r)) :
    StrictMonoOn (fun u => scalarGradientAngle ψ (projectionAffineTime t r σ c u, q))
      (Icc c (c + 1)) := by
  intro a ha b hb hab
  have ha' := projectionAffineTime_mem_closedBall t r σ c a hr.le hσ ha
  have hb' := projectionAffineTime_mem_closedBall t r σ c b hr.le hσ hb
  rcases hσ with rfl | rfl
  · have ht : projectionAffineTime t r 1 c a < projectionAffineTime t r 1 c b := by
      dsimp [projectionAffineTime]
      nlinarith
    simpa only [one_mul] using hm ha' hb' ht
  · have ht : projectionAffineTime t r (-1) c b < projectionAffineTime t r (-1) c a := by
      dsimp [projectionAffineTime]
      nlinarith
    simpa only [neg_one_mul, neg_lt_neg_iff] using hm hb' ha' ht

/-- The strictly positive derivative after reversal is established by
the chain rule, uniformly for every auxiliary parameter in the box. -/
theorem scalarGradientAngle_deriv_pos_affineTime
    {ψ : ℝ × Plane → ℝ} (t r σ c u : ℝ) (q : Plane)
    (hr : 0 < r)
    (hψ : AnalyticAt ℝ ψ (projectionAffineTime t r σ c u, q))
    (hh : scalarHeadDerivative ψ (projectionAffineTime t r σ c u, q) ≠ 0)
    (hd : 0 < σ * deriv (fun s => scalarGradientSlope ψ (s, q))
      (projectionAffineTime t r σ c u)) :
    0 < deriv (fun v => scalarGradientAngle ψ (projectionAffineTime t r σ c v, q)) u := by
  have hdiff : DifferentiableAt ℝ (fun s => scalarGradientAngle ψ (s, q))
      (projectionAffineTime t r σ c u) :=
    Real.differentiable_arctan.differentiableAt.comp _
      (((scalarGradientSlope_analyticAt hψ hh).comp
        (f := fun s : ℝ => (s, q)) (analyticAt_id.prod analyticAt_const)).differentiableAt)
  rw [deriv_comp_projectionAffineTime t r σ c u hdiff]
  have hp := mul_pos (mul_pos (show (0 : ℝ) < 2 by norm_num) hr)
    (scalarGradientAngle_oriented_deriv_pos σ hψ hh hd)
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hp

/-- Nonstationarity gives an actual analytic projection on any chosen
unit time interval. Its head gradient never vanishes, and every angle
slice is strictly increasing, with strictly positive derivative through
both boundary faces of the closed box. -/
theorem exists_reparametrizeScalarProjection_patch
    {ψ : ℝ × Plane → ℝ} {U : Set (ℝ × Plane)} (hU : IsOpen U)
    {p : ℝ × Plane} (hp : p ∈ U) (hψ : AnalyticAt ℝ ψ p)
    (hh : scalarHeadDerivative ψ p ≠ 0)
    (hd : deriv (fun t => scalarGradientSlope ψ (t, p.2)) p.1 ≠ 0)
    (c : ℝ) :
    ∃ r : ℝ, 0 < r ∧ ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      (∀ z ∈ Icc c (c + 1) ×ˢ closedBall p.2 r,
        (projectionAffineTime p.1 r σ c z.1, z.2) ∈ U ∧
        AnalyticAt ℝ (reparametrizeScalarProjection ψ p.1 r σ c) z ∧
        scalarHeadDerivative (reparametrizeScalarProjection ψ p.1 r σ c) z ≠ 0 ∧
        0 < deriv (fun v => scalarGradientAngle
          (reparametrizeScalarProjection ψ p.1 r σ c) (v, z.2)) z.1) ∧
      ∀ q ∈ closedBall p.2 r,
        StrictMonoOn (fun u => scalarGradientAngle
          (reparametrizeScalarProjection ψ p.1 r σ c) (u, q)) (Icc c (c + 1)) := by
  obtain ⟨r, hr, σ, hσ, hdom, hbox, hm⟩ :=
    exists_scalarGradientSlope_monotone_patch hU hp hψ hh hd
  have hin (z : ℝ × Plane) (hz : z ∈ Icc c (c + 1) ×ˢ closedBall p.2 r) :
      (projectionAffineTime p.1 r σ c z.1, z.2) ∈ closedBall p r := by
    rw [← closedBall_prod_same]
    exact ⟨projectionAffineTime_mem_closedBall _ _ _ _ _ hr.le hσ hz.1, hz.2⟩
  refine ⟨r, hr, σ, hσ, ?_, ?_⟩
  · intro z hz
    obtain ⟨ha, hh, hd⟩ := hbox _ (hin z hz)
    refine ⟨hdom (hin z hz), reparametrizeScalarProjection_analyticAt _ _ _ _ _ ha,
      ?_, ?_⟩
    · rwa [(reparametrizeScalarProjection_parameterDerivatives _ _ _ _ _ ha).1]
    · rw [reparametrizeScalarProjection_angle_deriv _ _ _ _ _ _ ha]
      exact scalarGradientAngle_deriv_pos_affineTime _ _ _ _ _ _ hr ha hh hd
  · intro q hq a ha b hb hab
    have hmono := scalarGradientAngle_strictMonoOn_affineTime p.1 r σ c q hr hσ
      (scalarGradientAngle_strictMonoOn hσ (hm q hq))
    dsimp only
    rw [reparametrizeScalarProjection_angle _ _ _ _ _ (hbox _ (hin (a, q) ⟨ha, hq⟩)).1,
      reparametrizeScalarProjection_angle _ _ _ _ _ (hbox _ (hin (b, q) ⟨hb, hq⟩)).1]
    exact hmono ha hb hab

/-- The two families can share one time axis while remaining separated
by a gap. The cutoff lies strictly between the closed unit intervals. -/
def joinedScalarProjection (φ ψ : ℝ × Plane → ℝ) (p : ℝ × Plane) : ℝ :=
  if p.1 < (3 : ℝ) / 2 then φ p else ψ p

theorem joinedScalarProjection_eventuallyEq_left
    (φ ψ : ℝ × Plane → ℝ) {p : ℝ × Plane} (hp : p.1 < (3 : ℝ) / 2) :
    joinedScalarProjection φ ψ =ᶠ[𝓝 p] φ := by
  filter_upwards [continuousAt_fst.preimage_mem_nhds (isOpen_Iio.mem_nhds hp)]
    with z hz
  exact if_pos hz

theorem joinedScalarProjection_eventuallyEq_right
    (φ ψ : ℝ × Plane → ℝ) {p : ℝ × Plane} (hp : (3 : ℝ) / 2 < p.1) :
    joinedScalarProjection φ ψ =ᶠ[𝓝 p] ψ := by
  filter_upwards [continuousAt_fst.preimage_mem_nhds (isOpen_Ioi.mem_nhds hp)]
    with z hz
  exact if_neg (not_lt.mpr hz.le)

theorem joinedScalarProjection_analyticAt_left
    {φ ψ : ℝ × Plane → ℝ} {p : ℝ × Plane}
    (hp : p.1 < (3 : ℝ) / 2) (hφ : AnalyticAt ℝ φ p) :
    AnalyticAt ℝ (joinedScalarProjection φ ψ) p :=
  hφ.congr (joinedScalarProjection_eventuallyEq_left φ ψ hp).symm

theorem joinedScalarProjection_analyticAt_right
    {φ ψ : ℝ × Plane → ℝ} {p : ℝ × Plane}
    (hp : (3 : ℝ) / 2 < p.1) (hψ : AnalyticAt ℝ ψ p) :
    AnalyticAt ℝ (joinedScalarProjection φ ψ) p :=
  hψ.congr (joinedScalarProjection_eventuallyEq_right φ ψ hp).symm

theorem joinedScalarProjection_angle_left
    (φ ψ : ℝ × Plane → ℝ) {p : ℝ × Plane} (hp : p.1 < (3 : ℝ) / 2) :
    scalarGradientAngle (joinedScalarProjection φ ψ) p = scalarGradientAngle φ p := by
  simp only [scalarGradientAngle, scalarGradientSlope, scalarHeadDerivative,
    scalarTailDerivative, (joinedScalarProjection_eventuallyEq_left φ ψ hp).fderiv_eq]

theorem joinedScalarProjection_angle_right
    (φ ψ : ℝ × Plane → ℝ) {p : ℝ × Plane} (hp : (3 : ℝ) / 2 < p.1) :
    scalarGradientAngle (joinedScalarProjection φ ψ) p = scalarGradientAngle ψ p := by
  simp only [scalarGradientAngle, scalarGradientSlope, scalarHeadDerivative,
    scalarTailDerivative, (joinedScalarProjection_eventuallyEq_right φ ψ hp).fderiv_eq]

/-- Joining increasing slices with ordered, separated angle ranges gives
strict monotonicity on the full disconnected time domain. -/
theorem joinedScalarProjection_angle_strictMonoOn
    (φ ψ : ℝ × Plane → ℝ) (q : Plane)
    (hφ : StrictMonoOn (fun u => scalarGradientAngle φ (u, q)) (Icc (0 : ℝ) 1))
    (hψ : StrictMonoOn (fun u => scalarGradientAngle ψ (u, q)) (Icc (2 : ℝ) 3))
    (hsep : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (2 : ℝ) 3,
      scalarGradientAngle φ (u, q) < scalarGradientAngle ψ (v, q)) :
    StrictMonoOn (fun u => scalarGradientAngle (joinedScalarProjection φ ψ) (u, q))
      (Icc (0 : ℝ) 1 ∪ Icc (2 : ℝ) 3) := by
  intro a ha b hb hab
  dsimp only
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · rw [joinedScalarProjection_angle_left φ ψ (by dsimp; linarith [ha.2]),
      joinedScalarProjection_angle_left φ ψ (by dsimp; linarith [hb.2])]
    exact hφ ha hb hab
  · rw [joinedScalarProjection_angle_left φ ψ (by dsimp; linarith [ha.2]),
      joinedScalarProjection_angle_right φ ψ (by dsimp; linarith [hb.1])]
    exact hsep a ha b hb
  · linarith [ha.1, hb.2]
  · rw [joinedScalarProjection_angle_right φ ψ (by dsimp; linarith [ha.1]),
      joinedScalarProjection_angle_right φ ψ (by dsimp; linarith [hb.1])]
    exact hψ ha hb hab

end PlanarNikodym
