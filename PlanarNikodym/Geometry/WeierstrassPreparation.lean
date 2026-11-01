import PlanarNikodym.Geometry.WeierstrassBanachPreparation
import PlanarNikodym.Geometry.AnalyticCoefficientLift
import PlanarNikodym.Geometry.AnalyticCoefficientUniqueness
import PlanarNikodym.Geometry.AnalyticSequenceEvaluation
import PlanarNikodym.Geometry.AnalyticWeierstrassNormalization

/-! Convergent real Weierstrass preparation at an arbitrary finite vertical order.
The polynomial coefficients and the nonvanishing unit are constructed from the actual
joint analytic germ. No formal factorization or analytic preparation input is assumed. -/

noncomputable section
open Set Filter
open scoped Topology ENNReal

namespace PlanarNikodym

theorem weierstrass_monic_rescaling (m : ℕ) (a : Fin m → ℝ) (s t : ℝ)
    (hs : s ≠ 0) :
    s ^ m * ((t / s) ^ m + ∑ i : Fin m, a i * (t / s) ^ (i : ℕ)) =
      t ^ m + ∑ i : Fin m, (a i * s ^ m / s ^ (i : ℕ)) * t ^ (i : ℕ) := by
  rw [mul_add, Finset.mul_sum, div_pow]
  congr 1
  · field_simp
  · apply Finset.sum_congr rfl
    intro i _
    rw [div_pow]
    ring

/-- Genuine convergent Weierstrass preparation, including multiple roots and order zero.
The lower polynomial coefficients vanish at the distinguished parameter, and the scalar
unit is jointly analytic and nonzero on a neighborhood. -/
theorem exists_analytic_weierstrass_preparation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E × ℝ → ℝ) (x₀ : E) (t₀ : ℝ) (m : ℕ)
    (hf : AnalyticAt ℝ f (x₀, t₀))
    (hzero : ∀ j < m, iteratedDeriv j (fun t => f (x₀, t)) t₀ = 0)
    (hm : iteratedDeriv m (fun t => f (x₀, t)) t₀ ≠ 0) :
    ∃ (a : E → Fin m → ℝ) (u : E × ℝ → ℝ),
      AnalyticAt ℝ a x₀ ∧ a x₀ = 0 ∧
      AnalyticAt ℝ u (x₀, t₀) ∧ u (x₀, t₀) ≠ 0 ∧
      ∀ᶠ z in 𝓝 (x₀, t₀),
        u z ≠ 0 ∧ f z =
          ((z.2 - t₀) ^ m + ∑ i : Fin m, a z.1 i * (z.2 - t₀) ^ (i : ℕ)) * u z := by
  obtain ⟨v, hv, hv₀, hH, hbase, hmul⟩ :=
    exists_analytic_weierstrass_normalization f x₀ t₀ m hf hzero hm
  let H : E × ℝ → ℝ := fun z => f z / v z.2
  obtain ⟨s, hs, F, hF, hsum⟩ := exists_analytic_coefficient_lift H x₀ t₀ hH
  have hs₀ : s ≠ 0 := ne_of_gt hs
  have hsm : s ^ m ≠ 0 := pow_ne_zero _ hs₀
  have hF₀ : F x₀ = s ^ m • lp.single ∞ m (1 : ℝ) :=
    coefficient_lift_eq_single_of_normalized_fiber H F x₀ t₀ s m hs₀ hsum
      (hbase.mono fun _ h => h.2)
  obtain ⟨b, q, hb, hq, hb₀, hq₀, hfac⟩ :=
    exists_weierstrass_banach_preparation F x₀ m (s ^ m) hsm hF hF₀
  let a : E → Fin m → ℝ := fun x i => b x i * s ^ m / s ^ (i : ℕ)
  let u : E × ℝ → ℝ := fun z =>
    weierstrassSeriesEval (q z.1) ((z.2 - t₀) / s) * v z.2 / s ^ m
  have ha : AnalyticAt ℝ a x₀ := by
    apply AnalyticAt.pi
    intro i
    exact ((analyticAt_pi_iff.mp hb i).mul analyticAt_const).div analyticAt_const
      (pow_ne_zero _ hs₀)
  have ha₀ : a x₀ = 0 := by
    ext i
    simp [a, hb₀]
  have ht : AnalyticAt ℝ (fun z : E × ℝ => (z.2 - t₀) / s) (x₀, t₀) :=
    (analyticAt_snd.sub analyticAt_const).div analyticAt_const hs₀
  have hq' : AnalyticAt ℝ (fun z : E × ℝ => q z.1) (x₀, t₀) :=
    AnalyticAt.comp (x := (x₀, t₀)) (f := fun z : E × ℝ => z.1) (g := q)
      hq analyticAt_fst
  have he : AnalyticAt ℝ
      (fun z : E × ℝ => weierstrassSeriesEval (q z.1) ((z.2 - t₀) / s)) (x₀, t₀) :=
    AnalyticAt.weierstrassSeriesEval hq' ht (by simp)
  have hu : AnalyticAt ℝ u (x₀, t₀) :=
    (he.mul (hv.comp analyticAt_snd)).div analyticAt_const hsm
  have hu₀ : u (x₀, t₀) = v t₀ := by
    simp [u, hq₀, hsm]
  have hun : u (x₀, t₀) ≠ 0 := hu₀ ▸ hv₀
  have htnear : ∀ᶠ z : E × ℝ in 𝓝 (x₀, t₀), |(z.2 - t₀) / s| < 1 := by
    have hc : ContinuousAt (fun _ : E × ℝ => (1 : ℝ)) (x₀, t₀) := continuousAt_const
    simpa only [Real.norm_eq_abs] using
      ht.continuousAt.norm.eventually_lt hc (by simp)
  refine ⟨a, u, ha, ha₀, hu, hun, ?_⟩
  filter_upwards [hu.continuousAt.eventually_ne hun, htnear, hsum, hmul,
    continuous_fst.continuousAt.eventually hfac] with z hzu hzt hzs hzm hzf
  refine ⟨hzu, ?_⟩
  have heq : H z =
      (((z.2 - t₀) / s) ^ m +
        ∑ i : Fin m, b z.1 i * ((z.2 - t₀) / s) ^ (i : ℕ)) *
        weierstrassSeriesEval (q z.1) ((z.2 - t₀) / s) := by
    calc
      H z = weierstrassSeriesEval (F z.1) ((z.2 - t₀) / s) := hzs.tsum_eq.symm
      _ = _ := by
        rw [hzf.2]
        exact weierstrassSeriesEval_preparation m (b z.1) (q z.1) hzt
  have hscale := weierstrass_monic_rescaling m (b z.1) s (z.2 - t₀) hs₀
  change f z = _ * (_ * _ / _)
  rw [hzm.2]
  change H z * v z.2 = _
  rw [heq, ← hscale]
  field_simp

/-- Preparation on an actual product of open neighborhoods, with jointly analytic unit
nonvanishing everywhere on that product and analytic coefficients throughout the base. -/
theorem exists_analytic_weierstrass_preparation_on
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E × ℝ → ℝ) (x₀ : E) (t₀ : ℝ) (m : ℕ)
    (hf : AnalyticAt ℝ f (x₀, t₀))
    (hzero : ∀ j < m, iteratedDeriv j (fun t => f (x₀, t)) t₀ = 0)
    (hm : iteratedDeriv m (fun t => f (x₀, t)) t₀ ≠ 0) :
    ∃ (U : Set E) (V : Set ℝ) (a : E → Fin m → ℝ) (u : E × ℝ → ℝ),
      IsOpen U ∧ x₀ ∈ U ∧ IsOpen V ∧ t₀ ∈ V ∧
      AnalyticOnNhd ℝ a U ∧ a x₀ = 0 ∧
      AnalyticOnNhd ℝ u (U ×ˢ V) ∧ (∀ z ∈ U ×ˢ V, u z ≠ 0) ∧
      ∀ z ∈ U ×ˢ V, f z =
        ((z.2 - t₀) ^ m + ∑ i : Fin m, a z.1 i * (z.2 - t₀) ^ (i : ℕ)) * u z := by
  obtain ⟨a, u, ha, ha₀, hu, _, heq⟩ :=
    exists_analytic_weierstrass_preparation f x₀ t₀ m hf hzero hm
  have hall : {z : E × ℝ |
      AnalyticAt ℝ a z.1 ∧ AnalyticAt ℝ u z ∧ u z ≠ 0 ∧ f z =
        ((z.2 - t₀) ^ m + ∑ i : Fin m, a z.1 i * (z.2 - t₀) ^ (i : ℕ)) * u z}
      ∈ 𝓝 (x₀, t₀) := by
    filter_upwards [continuous_fst.continuousAt.eventually ha.eventually_analyticAt,
      hu.eventually_analyticAt, heq] with z hza hzu hze
    exact ⟨hza, hzu, hze⟩
  obtain ⟨U, V, hU, hxU, hV, htV, hUV⟩ := mem_nhds_prod_iff'.mp hall
  refine ⟨U, V, a, u, hU, hxU, hV, htV, ?_, ha₀, ?_, ?_, ?_⟩
  · intro x hx
    exact (hUV (show (x, t₀) ∈ U ×ˢ V from ⟨hx, htV⟩)).1
  · intro z hz
    exact (hUV hz).2.1
  · intro z hz
    exact (hUV hz).2.2.1
  · intro z hz
    exact (hUV hz).2.2.2

end PlanarNikodym
