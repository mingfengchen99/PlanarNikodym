import PlanarNikodym.Geometry.AnalyticCoefficientLift
import PlanarNikodym.Geometry.AnalyticSequenceEvaluation
import PlanarNikodym.Geometry.WeierstrassBanachDivision
import PlanarNikodym.Geometry.WeierstrassPreparation

/-! Convergent real analytic division by a parameter-dependent monic
polynomial, and by its product with an analytic unit. Numerators are
arbitrary joint analytic germs, with their own radius of convergence. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Actual division by a monic polynomial of arbitrary degree, including
degree zero. Lower coefficients vanish at the base parameter; the
numerator is any joint analytic germ. -/
theorem exists_analytic_monic_polynomial_division
    {m : ℕ} (g : E × ℝ → ℝ) (a : E → Fin m → ℝ) (x₀ : E) (t₀ : ℝ)
    (hg : AnalyticAt ℝ g (x₀, t₀)) (ha : AnalyticAt ℝ a x₀) (ha₀ : a x₀ = 0) :
    ∃ (q : E × ℝ → ℝ) (r : E → Fin m → ℝ),
      AnalyticAt ℝ q (x₀, t₀) ∧ AnalyticAt ℝ r x₀ ∧
      ∀ᶠ z in 𝓝 (x₀, t₀),
        g z = q z * ((z.2 - t₀) ^ m +
          ∑ i : Fin m, a z.1 i * (z.2 - t₀) ^ (i : ℕ)) +
          ∑ i : Fin m, r z.1 i * (z.2 - t₀) ^ (i : ℕ) := by
  obtain ⟨s, hs, G, hG, hsum⟩ := exists_analytic_coefficient_lift g x₀ t₀ hg
  have hsn : s ≠ 0 := hs.ne'
  let b : E → Fin m → ℝ := fun x i => a x i * s ^ (i : ℕ) / s ^ m
  have hb : AnalyticAt ℝ b x₀ := by
    apply AnalyticAt.pi
    intro i
    exact (((ContinuousLinearMap.proj i).analyticAt _ |>.comp ha).mul analyticAt_const).div
      analyticAt_const (pow_ne_zero m hsn)
  have hb₀ : b x₀ = 0 := by
    ext i
    simp [b, ha₀]
  obtain ⟨R, Q, hR, hQ, _, _, hdivision⟩ :=
    exists_weierstrass_banach_division b G x₀ hb hb₀ hG
  let T : E × ℝ → ℝ := fun z => (z.2 - t₀) / s
  have hT : AnalyticAt ℝ T (x₀, t₀) :=
    (analyticAt_snd.sub analyticAt_const).div analyticAt_const hsn
  have hQT : AnalyticAt ℝ
      (fun z : E × ℝ => weierstrassSeriesEval (Q z.1) (T z)) (x₀, t₀) :=
    AnalyticAt.weierstrassSeriesEval
      (hQ.comp (f := fun z : E × ℝ => z.1) analyticAt_fst) hT
      (by simp [T])
  let q : E × ℝ → ℝ := fun z => weierstrassSeriesEval (Q z.1) (T z) / s ^ m
  let r : E → Fin m → ℝ := fun x i => R x i / s ^ (i : ℕ)
  refine ⟨q, r, hQT.div analyticAt_const (pow_ne_zero m hsn), ?_, ?_⟩
  · apply AnalyticAt.pi
    intro i
    exact ((ContinuousLinearMap.proj i).analyticAt _ |>.comp hR).div analyticAt_const
      (pow_ne_zero i.val hsn)
  · have hsmall : ∀ᶠ z in 𝓝 (x₀, t₀), |T z| < 1 :=
      hT.continuousAt.abs.eventually_lt continuousAt_const (by simp [T])
    filter_upwards [hsum, continuous_fst.continuousAt.eventually hdivision, hsmall]
      with z hz hd ht
    have he : g z =
        (∑ i : Fin m, R z.1 i * T z ^ (i : ℕ)) +
          (T z ^ m + ∑ i : Fin m, b z.1 i * T z ^ (i : ℕ)) *
            weierstrassSeriesEval (Q z.1) (T z) := by
      calc
        g z = weierstrassSeriesEval (G z.1) (T z) := hz.tsum_eq.symm
        _ = _ := by
          rw [hd, weierstrassSeriesEval_add _ _ ht, weierstrassSeriesEval_sum _ _ ht]
          simp only [weierstrassSeriesEval_smul, weierstrassSeriesEval_single, one_mul,
            weierstrassPolynomialAction, weierstrassSeriesEval_preparation _ _ _ ht]
    have hpoly : T z ^ m + (∑ i : Fin m, b z.1 i * T z ^ (i : ℕ)) =
        ((z.2 - t₀) ^ m + ∑ i : Fin m, a z.1 i * (z.2 - t₀) ^ (i : ℕ)) / s ^ m := by
      rw [add_div, Finset.sum_div]
      congr 1
      · exact div_pow _ _ _
      · apply Finset.sum_congr rfl
        intro i _
        dsimp only [b, T]
        rw [div_pow]
        field_simp
    have hrem : (∑ i : Fin m, R z.1 i * T z ^ (i : ℕ)) =
        ∑ i : Fin m, r z.1 i * (z.2 - t₀) ^ (i : ℕ) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [r, T]
      rw [div_pow]
      ring
    rw [hpoly, hrem] at he
    dsimp only [q]
    rw [he]
    ring

/-- Division by an actual prepared germ. The quotient is divided by the
analytic unit; the finite remainder is unchanged. -/
theorem exists_analytic_prepared_division
    {m : ℕ} (f g u : E × ℝ → ℝ) (a : E → Fin m → ℝ) (x₀ : E) (t₀ : ℝ)
    (hg : AnalyticAt ℝ g (x₀, t₀)) (hu : AnalyticAt ℝ u (x₀, t₀))
    (hu₀ : u (x₀, t₀) ≠ 0) (ha : AnalyticAt ℝ a x₀) (ha₀ : a x₀ = 0)
    (hf : ∀ᶠ z in 𝓝 (x₀, t₀), f z = u z *
      ((z.2 - t₀) ^ m + ∑ i : Fin m, a z.1 i * (z.2 - t₀) ^ (i : ℕ))) :
    ∃ (q : E × ℝ → ℝ) (r : E → Fin m → ℝ),
      AnalyticAt ℝ q (x₀, t₀) ∧ AnalyticAt ℝ r x₀ ∧
      ∀ᶠ z in 𝓝 (x₀, t₀),
        g z = q z * f z + ∑ i : Fin m, r z.1 i * (z.2 - t₀) ^ (i : ℕ) := by
  obtain ⟨q, r, hq, hr, he⟩ :=
    exists_analytic_monic_polynomial_division g a x₀ t₀ hg ha ha₀
  refine ⟨fun z => q z / u z, r, hq.div hu hu₀, hr, ?_⟩
  filter_upwards [he, hf, hu.continuousAt.eventually_ne hu₀] with z he hf hun
  rw [hf]
  have hc (P : ℝ) : q z / u z * (u z * P) = q z * P := by field_simp
  rw [hc]
  exact he

/-- The monic division identity on an actual open product neighborhood,
with joint analyticity of the quotient throughout that neighborhood. -/
theorem exists_analytic_monic_polynomial_division_on
    {m : ℕ} (g : E × ℝ → ℝ) (a : E → Fin m → ℝ) (x₀ : E) (t₀ : ℝ)
    (hg : AnalyticAt ℝ g (x₀, t₀)) (ha : AnalyticAt ℝ a x₀) (ha₀ : a x₀ = 0) :
    ∃ (U : Set E) (V : Set ℝ) (q : E × ℝ → ℝ) (r : E → Fin m → ℝ),
      IsOpen U ∧ x₀ ∈ U ∧ IsOpen V ∧ t₀ ∈ V ∧
      AnalyticOnNhd ℝ q (U ×ˢ V) ∧ AnalyticOnNhd ℝ r U ∧
      ∀ z ∈ U ×ˢ V,
        g z = q z * ((z.2 - t₀) ^ m +
          ∑ i : Fin m, a z.1 i * (z.2 - t₀) ^ (i : ℕ)) +
          ∑ i : Fin m, r z.1 i * (z.2 - t₀) ^ (i : ℕ) := by
  obtain ⟨q, r, hq, hr, he⟩ :=
    exists_analytic_monic_polynomial_division g a x₀ t₀ hg ha ha₀
  have hall : {z : E × ℝ | AnalyticAt ℝ q z ∧ AnalyticAt ℝ r z.1 ∧
      g z = q z * ((z.2 - t₀) ^ m +
        ∑ i : Fin m, a z.1 i * (z.2 - t₀) ^ (i : ℕ)) +
        ∑ i : Fin m, r z.1 i * (z.2 - t₀) ^ (i : ℕ)} ∈ 𝓝 (x₀, t₀) := by
    filter_upwards [hq.eventually_analyticAt,
      continuous_fst.continuousAt.eventually hr.eventually_analyticAt, he]
      with z hqz hrz hez
    exact ⟨hqz, hrz, hez⟩
  obtain ⟨U, V, hU, hxU, hV, htV, hUV⟩ := mem_nhds_prod_iff'.mp hall
  exact ⟨U, V, q, r, hU, hxU, hV, htV, fun z hz => (hUV hz).1,
    fun x hx => (hUV (show (x, t₀) ∈ U ×ˢ V from ⟨hx, htV⟩)).2.1,
    fun z hz => (hUV hz).2.2⟩

/-- Convergent Weierstrass division by an arbitrary real analytic germ
of finite vertical order. Preparation is constructed inside the proof;
the caller supplies no factorization, quotient or remainder. -/
theorem exists_analytic_weierstrass_division
    (f g : E × ℝ → ℝ) (x₀ : E) (t₀ : ℝ) (m : ℕ)
    (hf : AnalyticAt ℝ f (x₀, t₀)) (hg : AnalyticAt ℝ g (x₀, t₀))
    (hzero : ∀ j < m, iteratedDeriv j (fun t => f (x₀, t)) t₀ = 0)
    (hm : iteratedDeriv m (fun t => f (x₀, t)) t₀ ≠ 0) :
    ∃ (q : E × ℝ → ℝ) (r : E → Fin m → ℝ),
      AnalyticAt ℝ q (x₀, t₀) ∧ AnalyticAt ℝ r x₀ ∧
      ∀ᶠ z in 𝓝 (x₀, t₀),
        g z = q z * f z + ∑ i : Fin m, r z.1 i * (z.2 - t₀) ^ (i : ℕ) := by
  obtain ⟨a, u, ha, ha₀, hu, hu₀, hfactor⟩ :=
    exists_analytic_weierstrass_preparation f x₀ t₀ m hf hzero hm
  apply exists_analytic_prepared_division f g u a x₀ t₀ hg hu hu₀ ha ha₀
  filter_upwards [hfactor] with z hz
  exact hz.2.trans (mul_comm _ _)

/-- The general division theorem on a genuine open product neighborhood.
The quotient is jointly analytic and each finite remainder coefficient
is analytic in the parameter on the whole returned neighborhood. -/
theorem exists_analytic_weierstrass_division_on
    (f g : E × ℝ → ℝ) (x₀ : E) (t₀ : ℝ) (m : ℕ)
    (hf : AnalyticAt ℝ f (x₀, t₀)) (hg : AnalyticAt ℝ g (x₀, t₀))
    (hzero : ∀ j < m, iteratedDeriv j (fun t => f (x₀, t)) t₀ = 0)
    (hm : iteratedDeriv m (fun t => f (x₀, t)) t₀ ≠ 0) :
    ∃ (U : Set E) (V : Set ℝ) (q : E × ℝ → ℝ) (r : E → Fin m → ℝ),
      IsOpen U ∧ x₀ ∈ U ∧ IsOpen V ∧ t₀ ∈ V ∧
      AnalyticOnNhd ℝ q (U ×ˢ V) ∧ AnalyticOnNhd ℝ r U ∧
      ∀ z ∈ U ×ˢ V,
        g z = q z * f z + ∑ i : Fin m, r z.1 i * (z.2 - t₀) ^ (i : ℕ) := by
  obtain ⟨q, r, hq, hr, he⟩ :=
    exists_analytic_weierstrass_division f g x₀ t₀ m hf hg hzero hm
  have hall : {z : E × ℝ | AnalyticAt ℝ q z ∧ AnalyticAt ℝ r z.1 ∧
      g z = q z * f z + ∑ i : Fin m, r z.1 i * (z.2 - t₀) ^ (i : ℕ)} ∈
      𝓝 (x₀, t₀) := by
    filter_upwards [hq.eventually_analyticAt,
      continuous_fst.continuousAt.eventually hr.eventually_analyticAt, he]
      with z hqz hrz hez
    exact ⟨hqz, hrz, hez⟩
  obtain ⟨U, V, hU, hxU, hV, htV, hUV⟩ := mem_nhds_prod_iff'.mp hall
  exact ⟨U, V, q, r, hU, hxU, hV, htV, fun z hz => (hUV hz).1,
    fun x hx => (hUV (show (x, t₀) ∈ U ×ˢ V from ⟨hx, htV⟩)).2.1,
    fun z hz => (hUV hz).2.2⟩

end PlanarNikodym
