import PlanarNikodym.Geometry.AnalyticWeierstrassUniqueness

/-! Uniqueness of the actual monic polynomial and unit in Weierstrass preparation. -/

noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two monic factorizations of the same degree have the same coefficient and unit germs.
Only the second coefficient vector needs to be assumed analytic and to vanish at the
base point; division uniqueness then identifies it with the first one. -/
theorem analytic_weierstrass_preparation_unique
    {m : ℕ} (a b : E → Fin m → ℝ) (u v : E × ℝ → ℝ)
    (x₀ : E) (t₀ : ℝ)
    (hb : AnalyticAt ℝ b x₀) (hb₀ : b x₀ = 0)
    (hu : AnalyticAt ℝ u (x₀, t₀)) (hv : AnalyticAt ℝ v (x₀, t₀))
    (hu₀ : u (x₀, t₀) ≠ 0)
    (heq : ∀ᶠ z in 𝓝 (x₀, t₀),
      ((z.2 - t₀) ^ m +
        ∑ i : Fin m, a z.1 i * (z.2 - t₀) ^ (i : ℕ)) * u z =
      ((z.2 - t₀) ^ m +
        ∑ i : Fin m, b z.1 i * (z.2 - t₀) ^ (i : ℕ)) * v z) :
    a =ᶠ[𝓝 x₀] b ∧ u =ᶠ[𝓝 (x₀, t₀)] v := by
  have hun : ∀ᶠ z in 𝓝 (x₀, t₀), u z ≠ 0 :=
    hu.continuousAt.eventually_ne hu₀
  have he : ∀ᶠ z in 𝓝 (x₀, t₀),
      (v z / u z - 1) * ((z.2 - t₀) ^ m +
        ∑ i : Fin m, b z.1 i * (z.2 - t₀) ^ (i : ℕ)) +
        ∑ i : Fin m, (b z.1 i - a z.1 i) * (z.2 - t₀) ^ (i : ℕ) = 0 := by
    filter_upwards [heq, hun] with z hz huz
    simp only [sub_mul, Finset.sum_sub_distrib]
    apply (mul_right_cancel₀ huz)
    simp only [zero_mul]
    field_simp
    nlinarith only [hz]
  obtain ⟨hq, hr⟩ := analytic_monic_polynomial_division_eq_zero
    b (fun z => v z / u z - 1) (fun x i => b x i - a x i)
    x₀ t₀ hb hb₀ ((hv.div hu hu₀).sub analyticAt_const) he
  constructor
  · filter_upwards [hr] with x hx
    funext i
    exact (sub_eq_zero.mp (congrFun hx i)).symm
  · filter_upwards [hq, hun] with z hz huz
    have hratio : v z / u z = 1 := sub_eq_zero.mp hz
    simpa only [one_mul] using ((div_eq_iff huz).mp hratio).symm

/-- Convergent Weierstrass preparation exists and is unique as a germ, for every
finite vertical order, including order zero. The representatives are not claimed to
be equal away from a neighborhood of the base point. -/
theorem exists_analytic_weierstrass_preparation_unique
    [CompleteSpace E] (f : E × ℝ → ℝ) (x₀ : E) (t₀ : ℝ) (m : ℕ)
    (hf : AnalyticAt ℝ f (x₀, t₀))
    (hzero : ∀ j < m, iteratedDeriv j (fun t => f (x₀, t)) t₀ = 0)
    (hm : iteratedDeriv m (fun t => f (x₀, t)) t₀ ≠ 0) :
    ∃ (a : E → Fin m → ℝ) (u : E × ℝ → ℝ),
      AnalyticAt ℝ a x₀ ∧ a x₀ = 0 ∧
      AnalyticAt ℝ u (x₀, t₀) ∧ u (x₀, t₀) ≠ 0 ∧
      (∀ᶠ z in 𝓝 (x₀, t₀),
        u z ≠ 0 ∧
        f z = ((z.2 - t₀) ^ m +
          ∑ i : Fin m, a z.1 i * (z.2 - t₀) ^ (i : ℕ)) * u z) ∧
      ∀ (b : E → Fin m → ℝ) (v : E × ℝ → ℝ),
        AnalyticAt ℝ b x₀ → b x₀ = 0 →
        AnalyticAt ℝ v (x₀, t₀) →
        (∀ᶠ z in 𝓝 (x₀, t₀),
          f z = ((z.2 - t₀) ^ m +
            ∑ i : Fin m, b z.1 i * (z.2 - t₀) ^ (i : ℕ)) * v z) →
        a =ᶠ[𝓝 x₀] b ∧ u =ᶠ[𝓝 (x₀, t₀)] v := by
  obtain ⟨a, u, ha, ha₀, hu, hu₀, he⟩ :=
    exists_analytic_weierstrass_preparation f x₀ t₀ m hf hzero hm
  refine ⟨a, u, ha, ha₀, hu, hu₀, he, ?_⟩
  intro b v hb hb₀ hv he'
  apply analytic_weierstrass_preparation_unique a b u v x₀ t₀ hb hb₀ hu hv hu₀
  filter_upwards [he, he'] with z hz hz'
  exact hz.2.symm.trans hz'

end PlanarNikodym
