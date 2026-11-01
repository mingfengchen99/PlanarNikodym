import PlanarNikodym.Geometry.WeierstrassDivisionInvertibility
import PlanarNikodym.Geometry.AnalyticWeierstrassCoefficientIdentity
import PlanarNikodym.Geometry.WeierstrassPreparation
import PlanarNikodym.Geometry.AnalyticWeierstrassDivision

/-! Uniqueness of convergent Weierstrass division as actual analytic germs. -/

noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A zero division identity by a prepared monic polynomial has zero analytic quotient
and zero finite remainder. No regularity assumption on the remainder is needed. -/
theorem analytic_monic_polynomial_division_eq_zero
    {m : ℕ} (a : E → Fin m → ℝ) (q : E × ℝ → ℝ) (r : E → Fin m → ℝ)
    (x₀ : E) (t₀ : ℝ) (ha : AnalyticAt ℝ a x₀) (ha₀ : a x₀ = 0)
    (hq : AnalyticAt ℝ q (x₀, t₀))
    (heq : ∀ᶠ z in 𝓝 (x₀, t₀),
      q z * ((z.2 - t₀) ^ m +
        ∑ i : Fin m, a z.1 i * (z.2 - t₀) ^ (i : ℕ)) +
        ∑ i : Fin m, r z.1 i * (z.2 - t₀) ^ (i : ℕ) = 0) :
    q =ᶠ[𝓝 (x₀, t₀)] 0 ∧ r =ᶠ[𝓝 x₀] 0 := by
  obtain ⟨s, hs, Q, hQ, hsum⟩ := exists_analytic_coefficient_lift q x₀ t₀ hq
  have hs₀ : s ≠ 0 := hs.ne'
  have hsm : s ^ m ≠ 0 := pow_ne_zero _ hs₀
  let b : E → Fin m → ℝ := fun x i => a x i * s ^ (i : ℕ) / s ^ m
  have hb : AnalyticAt ℝ b x₀ := by
    apply AnalyticAt.pi
    intro i
    exact ((analyticAt_pi_iff.mp ha i).mul analyticAt_const).div analyticAt_const hsm
  have hb₀ : b x₀ = 0 := by ext i; simp [b, ha₀]
  have hinj : ∀ᶠ x in 𝓝 x₀, Function.Injective (weierstrassDivisionOperator m (b x)) := by
    have hh := hb.continuousAt.eventually (show
      ∀ᶠ v in 𝓝 (b x₀), Function.Injective (weierstrassDivisionOperator m v) by
        rw [hb₀]
        exact eventually_weierstrassDivisionOperator_injective m)
    exact hh
  have hall : {z : E × ℝ |
      HasSum (fun n => Q z.1 n * ((z.2 - t₀) / s) ^ n) (q z) ∧
      q z * ((z.2 - t₀) ^ m +
        ∑ i : Fin m, a z.1 i * (z.2 - t₀) ^ (i : ℕ)) +
        ∑ i : Fin m, r z.1 i * (z.2 - t₀) ^ (i : ℕ) = 0} ∈ 𝓝 (x₀, t₀) :=
    hsum.and heq
  obtain ⟨U, V, hU, hxU, hV, htV, hUV⟩ := mem_nhds_prod_iff'.mp hall
  have hzero : ∀ᶠ x in 𝓝 x₀, r x = 0 ∧ Q x = 0 := by
    filter_upwards [hinj, hU.mem_nhds hxU] with x hix hx
    have hxs : ∀ᶠ t in 𝓝 t₀,
        HasSum (fun n => Q x n * ((t - t₀) / s) ^ n) (q (x, t)) := by
      filter_upwards [hV.mem_nhds htV] with t ht
      exact (hUV (show (x, t) ∈ U ×ˢ V from ⟨hx, ht⟩)).1
    have hxe : ∀ᶠ t in 𝓝 t₀,
        q (x, t) * ((t - t₀) ^ m +
          ∑ i : Fin m, a x i * (t - t₀) ^ (i : ℕ)) +
          ∑ i : Fin m, r x i * (t - t₀) ^ (i : ℕ) = 0 := by
      filter_upwards [hV.mem_nhds htV] with t ht
      exact (hUV (show (x, t) ∈ U ×ˢ V from ⟨hx, ht⟩)).2
    have hd := weierstrassDivisionOperator_eq_zero_of_scalar_identity m (a x) (r x)
      (Q x) t₀ s hs₀ (fun t => q (x, t)) hxs hxe
    have hp : ((fun i : Fin m => r x i * s ^ (i : ℕ)), s ^ m • Q x) = 0 :=
      hix (by simpa only [map_zero] using hd)
    constructor
    · ext i
      have hi := congrArg (fun w : WeierstrassFactors m => w.1 i) hp
      exact (mul_eq_zero.mp hi).resolve_right (pow_ne_zero _ hs₀)
    · have hi := congrArg (fun w : WeierstrassFactors m => w.2) hp
      exact (smul_eq_zero.mp hi).resolve_left hsm
  refine ⟨?_, hzero.mono fun _ h => h.1⟩
  filter_upwards [hsum, continuous_fst.continuousAt.eventually hzero] with z hzs hz
  have hh := hzs.tsum_eq
  simpa [hz.2] using hh.symm

/-- Uniqueness of the actual quotient and remainder for a prepared monic polynomial. -/
theorem analytic_monic_polynomial_division_unique
    {m : ℕ} (a : E → Fin m → ℝ) (g q₁ q₂ : E × ℝ → ℝ)
    (r₁ r₂ : E → Fin m → ℝ) (x₀ : E) (t₀ : ℝ)
    (ha : AnalyticAt ℝ a x₀) (ha₀ : a x₀ = 0)
    (hq₁ : AnalyticAt ℝ q₁ (x₀, t₀)) (hq₂ : AnalyticAt ℝ q₂ (x₀, t₀))
    (he₁ : ∀ᶠ z in 𝓝 (x₀, t₀),
      g z = q₁ z * ((z.2 - t₀) ^ m +
        ∑ i : Fin m, a z.1 i * (z.2 - t₀) ^ (i : ℕ)) +
        ∑ i : Fin m, r₁ z.1 i * (z.2 - t₀) ^ (i : ℕ))
    (he₂ : ∀ᶠ z in 𝓝 (x₀, t₀),
      g z = q₂ z * ((z.2 - t₀) ^ m +
        ∑ i : Fin m, a z.1 i * (z.2 - t₀) ^ (i : ℕ)) +
        ∑ i : Fin m, r₂ z.1 i * (z.2 - t₀) ^ (i : ℕ)) :
    q₁ =ᶠ[𝓝 (x₀, t₀)] q₂ ∧ r₁ =ᶠ[𝓝 x₀] r₂ := by
  have he : ∀ᶠ z in 𝓝 (x₀, t₀),
      (q₁ z - q₂ z) * ((z.2 - t₀) ^ m +
        ∑ i : Fin m, a z.1 i * (z.2 - t₀) ^ (i : ℕ)) +
        ∑ i : Fin m, (r₁ z.1 i - r₂ z.1 i) * (z.2 - t₀) ^ (i : ℕ) = 0 := by
    filter_upwards [he₁, he₂] with z h₁ h₂
    simp only [sub_mul, Finset.sum_sub_distrib]
    linarith
  obtain ⟨hq, hr⟩ := analytic_monic_polynomial_division_eq_zero
    a (fun z => q₁ z - q₂ z) (fun x i => r₁ x i - r₂ x i)
    x₀ t₀ ha ha₀ (hq₁.sub hq₂) he
  constructor
  · exact hq.mono fun _ h => sub_eq_zero.mp h
  · filter_upwards [hr] with x hx
    funext i
    exact sub_eq_zero.mp (congrFun hx i)

/-- The homogeneous uniqueness statement for any finite-order regular analytic divisor,
obtained by actual preparation rather than by a preparation assumption. -/
theorem analytic_weierstrass_division_eq_zero
    [CompleteSpace E] {m : ℕ} (f q : E × ℝ → ℝ) (r : E → Fin m → ℝ)
    (x₀ : E) (t₀ : ℝ)
    (hf : AnalyticAt ℝ f (x₀, t₀)) (hq : AnalyticAt ℝ q (x₀, t₀))
    (hzero : ∀ j < m, iteratedDeriv j (fun t => f (x₀, t)) t₀ = 0)
    (hm : iteratedDeriv m (fun t => f (x₀, t)) t₀ ≠ 0)
    (heq : ∀ᶠ z in 𝓝 (x₀, t₀),
      q z * f z + ∑ i : Fin m, r z.1 i * (z.2 - t₀) ^ (i : ℕ) = 0) :
    q =ᶠ[𝓝 (x₀, t₀)] 0 ∧ r =ᶠ[𝓝 x₀] 0 := by
  obtain ⟨a, u, ha, ha₀, hu, _, hprep⟩ :=
    exists_analytic_weierstrass_preparation f x₀ t₀ m hf hzero hm
  have he : ∀ᶠ z in 𝓝 (x₀, t₀),
      (q z * u z) * ((z.2 - t₀) ^ m +
        ∑ i : Fin m, a z.1 i * (z.2 - t₀) ^ (i : ℕ)) +
        ∑ i : Fin m, r z.1 i * (z.2 - t₀) ^ (i : ℕ) = 0 := by
    filter_upwards [heq, hprep] with z hz hp
    rw [hp.2] at hz
    nlinarith only [hz]
  obtain ⟨hqu, hr⟩ := analytic_monic_polynomial_division_eq_zero
    a (fun z => q z * u z) r x₀ t₀ ha ha₀ (hq.mul hu) he
  refine ⟨?_, hr⟩
  filter_upwards [hqu, hprep] with z hz hp
  exact (mul_eq_zero.mp hz).resolve_right hp.1

/-- Germ uniqueness of division by an arbitrary finite-order real analytic divisor.
The numerator and remainder need no additional regularity beyond the two given
identities; the quotient germs are genuinely jointly analytic. -/
theorem analytic_weierstrass_division_unique
    [CompleteSpace E] (f g q₁ q₂ : E × ℝ → ℝ) (x₀ : E) (t₀ : ℝ) (m : ℕ)
    (r₁ r₂ : E → Fin m → ℝ)
    (hf : AnalyticAt ℝ f (x₀, t₀))
    (hq₁ : AnalyticAt ℝ q₁ (x₀, t₀)) (hq₂ : AnalyticAt ℝ q₂ (x₀, t₀))
    (hzero : ∀ j < m, iteratedDeriv j (fun t => f (x₀, t)) t₀ = 0)
    (hm : iteratedDeriv m (fun t => f (x₀, t)) t₀ ≠ 0)
    (he₁ : ∀ᶠ z in 𝓝 (x₀, t₀),
      g z = q₁ z * f z + ∑ i : Fin m, r₁ z.1 i * (z.2 - t₀) ^ (i : ℕ))
    (he₂ : ∀ᶠ z in 𝓝 (x₀, t₀),
      g z = q₂ z * f z + ∑ i : Fin m, r₂ z.1 i * (z.2 - t₀) ^ (i : ℕ)) :
    q₁ =ᶠ[𝓝 (x₀, t₀)] q₂ ∧ r₁ =ᶠ[𝓝 x₀] r₂ := by
  have he : ∀ᶠ z in 𝓝 (x₀, t₀),
      (q₁ z - q₂ z) * f z +
        ∑ i : Fin m, (r₁ z.1 i - r₂ z.1 i) * (z.2 - t₀) ^ (i : ℕ) = 0 := by
    filter_upwards [he₁, he₂] with z h₁ h₂
    simp only [sub_mul, Finset.sum_sub_distrib]
    linarith
  obtain ⟨hq, hr⟩ := analytic_weierstrass_division_eq_zero
    f (fun z => q₁ z - q₂ z) (fun x i => r₁ x i - r₂ x i) x₀ t₀
    hf (hq₁.sub hq₂) hzero hm he
  constructor
  · exact hq.mono fun _ h => sub_eq_zero.mp h
  · filter_upwards [hr] with x hx
    funext i
    exact sub_eq_zero.mp (congrFun hx i)

/-- Complete convergent Weierstrass division: actual analytic quotient and remainder
exist and are unique as germs. A competing remainder does not need to be assumed analytic. -/
theorem exists_analytic_weierstrass_division_unique
    [CompleteSpace E] (f g : E × ℝ → ℝ) (x₀ : E) (t₀ : ℝ) (m : ℕ)
    (hf : AnalyticAt ℝ f (x₀, t₀)) (hg : AnalyticAt ℝ g (x₀, t₀))
    (hzero : ∀ j < m, iteratedDeriv j (fun t => f (x₀, t)) t₀ = 0)
    (hm : iteratedDeriv m (fun t => f (x₀, t)) t₀ ≠ 0) :
    ∃ (q : E × ℝ → ℝ) (r : E → Fin m → ℝ),
      AnalyticAt ℝ q (x₀, t₀) ∧ AnalyticAt ℝ r x₀ ∧
      (∀ᶠ z in 𝓝 (x₀, t₀),
        g z = q z * f z + ∑ i : Fin m, r z.1 i * (z.2 - t₀) ^ (i : ℕ)) ∧
      ∀ (q' : E × ℝ → ℝ) (r' : E → Fin m → ℝ),
        AnalyticAt ℝ q' (x₀, t₀) →
        (∀ᶠ z in 𝓝 (x₀, t₀),
          g z = q' z * f z + ∑ i : Fin m, r' z.1 i * (z.2 - t₀) ^ (i : ℕ)) →
        q =ᶠ[𝓝 (x₀, t₀)] q' ∧ r =ᶠ[𝓝 x₀] r' := by
  obtain ⟨q, r, hq, hr, he⟩ :=
    exists_analytic_weierstrass_division f g x₀ t₀ m hf hg hzero hm
  refine ⟨q, r, hq, hr, he, ?_⟩
  intro q' r' hq' he'
  exact analytic_weierstrass_division_unique f g q q' x₀ t₀ m r r'
    hf hq hq' hzero hm he he'

end PlanarNikodym
