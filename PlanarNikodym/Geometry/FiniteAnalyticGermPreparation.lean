import PlanarNikodym.Geometry.FiniteFamilyWeierstrassFrame

/-! A common actual preparation cylinder for every finite analytic germ
family, with identically zero germs treated on that same cylinder. No
nonflatness, direction, order or prepared polynomial is supplied as input. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace PlanarNikodym

theorem exists_finite_analytic_germ_preparation
    {d : ℕ} {J : Type*} [Fintype J]
    (f : J → (Fin (d + 1) → ℝ) → ℝ) (x₀ : Fin (d + 1) → ℝ)
    (ha : ∀ j, AnalyticAt ℝ (f j) x₀) :
    ∃ (e : ((Fin d → ℝ) × ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ)) (ε r : ℝ),
      0 < ε ∧ 0 < r ∧ ∀ j,
        (∀ z ∈ ball 0 ε ×ˢ Ioo (-r) r, f j (x₀ + e z) = 0) ∨
        ∃ (m : ℕ) (a : (Fin d → ℝ) → Fin m → ℝ) (u : ((Fin d → ℝ) × ℝ) → ℝ),
          AnalyticOnNhd ℝ a (ball 0 ε) ∧ a 0 = 0 ∧
          AnalyticOnNhd ℝ u (ball 0 ε ×ˢ Ioo (-r) r) ∧
          (∀ z ∈ ball 0 ε ×ˢ Ioo (-r) r, u z ≠ 0) ∧
          (∀ z ∈ ball 0 ε ×ˢ Ioo (-r) r,
            f j (x₀ + e z) = (weierstrassPolynomial (a z.1)).eval z.2 * u z) ∧
          ∀ x ∈ ball 0 ε, ∀ t : ℝ, (weierstrassPolynomial (a x)).eval t = 0 → |t| < r := by
  classical
  let K := {j : J // ¬ ∀ᶠ y in 𝓝 x₀, f j y = 0}
  obtain ⟨e, m, a, u, ε, r, hε, hr, han, hu, hun, hfactor, _⟩ :=
    exists_finite_family_weierstrass_frame (fun j : K => f j) x₀ (fun j => ha j) (fun j => j.property)
  have h0 : e (0, 0) = 0 := map_zero e
  have hc : ContinuousAt (fun z : (Fin d → ℝ) × ℝ => x₀ + e z) (0, 0) :=
    continuousAt_const.add e.continuous.continuousAt
  have ht : Tendsto (fun z : (Fin d → ℝ) × ℝ => x₀ + e z) (𝓝 (0, 0)) (𝓝 x₀) := by
    simpa only [h0, add_zero] using hc.tendsto
  have hzeroNear : ∀ᶠ z : (Fin d → ℝ) × ℝ in 𝓝 (0, 0),
      ∀ j : J, (∀ᶠ y in 𝓝 x₀, f j y = 0) → f j (x₀ + e z) = 0 := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hj : ∀ᶠ y in 𝓝 x₀, f j y = 0
    · filter_upwards [ht.eventually hj] with z hz _
      exact hz
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hj h))
  obtain ⟨U, V, hU, hxU, hV, hxV, hUV⟩ := mem_nhds_prod_iff'.mp hzeroNear
  obtain ⟨rV, hrV, hrVsub⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hxV)
  let r' := min r rV
  have hr' : 0 < r' := lt_min hr hrV
  have hsmall (t : ℝ) (ht : t ∈ Ioo (-r') r') : t ∈ Ioo (-r) r ∧ t ∈ V := by
    have hrt : |t| < r' := abs_lt.mpr ht
    have hmin : r' ≤ r ∧ r' ≤ rV := ⟨min_le_left _ _, min_le_right _ _⟩
    refine ⟨abs_lt.mp (hrt.trans_le hmin.1), hrVsub ?_⟩
    simpa only [mem_ball, Real.dist_eq, sub_zero] using hrt.trans_le hmin.2
  choose W hW hxW hroots using fun j : K => exists_open_nhds_weierstrass_roots_small
    (a j) 0 ((han j).1 0 (mem_ball_self hε)).continuousAt (han j).2 r' hr'
  have hbaseNear : {x : Fin d → ℝ | x ∈ ball 0 ε ∧ x ∈ U ∧ ∀ j : K, x ∈ W j} ∈ 𝓝 0 := by
    filter_upwards [ball_mem_nhds _ hε, hU.mem_nhds hxU,
      Filter.eventually_all.mpr (fun j => (hW j).mem_nhds (hxW j))] with x hx hxu hxw
    exact ⟨hx, hxu, hxw⟩
  obtain ⟨ε', hε', hbase⟩ := Metric.mem_nhds_iff.mp hbaseNear
  have hprod {z : (Fin d → ℝ) × ℝ} (hz : z ∈ ball 0 ε' ×ˢ Ioo (-r') r') :
      z ∈ ball 0 ε ×ˢ Ioo (-r) r := ⟨(hbase hz.1).1, (hsmall z.2 hz.2).1⟩
  refine ⟨e, ε', r', hε', hr', ?_⟩
  intro j
  by_cases hj : ∀ᶠ y in 𝓝 x₀, f j y = 0
  · left
    intro z hz
    exact hUV ⟨(hbase hz.1).2.1, (hsmall z.2 hz.2).2⟩ j hj
  · right
    let k : K := ⟨j, hj⟩
    refine ⟨m k, a k, u k, ?_, (han k).2, ?_, ?_, ?_, ?_⟩
    · exact fun x hx => (han k).1 x (hbase hx).1
    · exact fun z hz => hu k z (hprod hz)
    · exact fun z hz => hun k z (hprod hz)
    · exact fun z hz => hfactor k z (hprod hz)
    · exact fun x hx t hroot => hroots k x ((hbase hx).2.2 k) t hroot

end PlanarNikodym
