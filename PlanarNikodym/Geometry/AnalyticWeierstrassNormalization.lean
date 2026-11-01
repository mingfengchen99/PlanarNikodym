import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Constructions

/-!
# Normalizing the distinguished fiber of an analytic germ

The hypotheses use the actual iterated derivatives in the last real variable.
The analytic unit is obtained from one-variable analytic order. Dividing by this
unit is jointly analytic in all variables and makes the distinguished fiber
exactly a monomial. This is a preliminary normalization, not a preparation
theorem at a multiple root.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace PlanarNikodym

/-- Actual vanishing derivatives and the first nonzero derivative determine the
finite analytic order. -/
theorem analyticOrderAt_eq_of_iteratedDeriv
    {f : ℝ → ℝ} {t₀ : ℝ} {m : ℕ} (hf : AnalyticAt ℝ f t₀)
    (hzero : ∀ j < m, iteratedDeriv j f t₀ = 0)
    (hm : iteratedDeriv m f t₀ ≠ 0) :
    analyticOrderAt f t₀ = (m : ℕ∞) := by
  have hlo : (m : ℕ∞) ≤ analyticOrderAt f t₀ :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).mpr hzero
  have hnot : ¬ ((m + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt f t₀ := by
    intro h
    exact hm ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).mp h
      m (Nat.lt_succ_self m))
  have hhi : analyticOrderAt f t₀ < (m : ℕ∞) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using lt_of_not_ge hnot
  exact le_antisymm (ENat.lt_coe_add_one_iff.mp hhi) hlo

/-- The unit in a one-variable finite-order factorization is constructed from
analyticity and actual derivative data. The order may also be zero. -/
theorem exists_analytic_unit_of_iteratedDeriv
    {f : ℝ → ℝ} {t₀ : ℝ} {m : ℕ} (hf : AnalyticAt ℝ f t₀)
    (hzero : ∀ j < m, iteratedDeriv j f t₀ = 0)
    (hm : iteratedDeriv m f t₀ ≠ 0) :
    ∃ u : ℝ → ℝ, AnalyticAt ℝ u t₀ ∧ u t₀ ≠ 0 ∧
      ∀ᶠ t in 𝓝 t₀, f t = (t - t₀) ^ m * u t := by
  obtain ⟨u, hu, hu0, heq⟩ := hf.analyticOrderAt_eq_natCast.mp
    (analyticOrderAt_eq_of_iteratedDeriv hf hzero hm)
  exact ⟨u, hu, hu0, by simpa only [smul_eq_mul] using heq⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Joint analyticity of the normalized germ requires only the scalar unit to
be analytic and nonzero at the distinguished coordinate. -/
theorem analyticAt_div_vertical_unit
    {f : E × ℝ → ℝ} {u : ℝ → ℝ} {x₀ : E} {t₀ : ℝ}
    (hf : AnalyticAt ℝ f (x₀, t₀)) (hu : AnalyticAt ℝ u t₀)
    (hu0 : u t₀ ≠ 0) :
    AnalyticAt ℝ (fun z : E × ℝ => f z / u z.2) (x₀, t₀) :=
  hf.div (hu.comp analyticAt_snd) hu0

/-- Normalization of an arbitrary finite vertical order. In particular the
normalizing factor depends only on the vertical variable, while the quotient
is genuinely jointly analytic. Both the factorization and nonvanishing hold
on a neighborhood of the original joint base point. -/
theorem exists_analytic_weierstrass_normalization
    (f : E × ℝ → ℝ) (x₀ : E) (t₀ : ℝ) (m : ℕ)
    (hf : AnalyticAt ℝ f (x₀, t₀))
    (hzero : ∀ j < m, iteratedDeriv j (fun t => f (x₀, t)) t₀ = 0)
    (hm : iteratedDeriv m (fun t => f (x₀, t)) t₀ ≠ 0) :
    ∃ u : ℝ → ℝ,
      AnalyticAt ℝ u t₀ ∧ u t₀ ≠ 0 ∧
      AnalyticAt ℝ (fun z : E × ℝ => f z / u z.2) (x₀, t₀) ∧
      (∀ᶠ t in 𝓝 t₀, f (x₀, t) = (t - t₀) ^ m * u t ∧
        f (x₀, t) / u t = (t - t₀) ^ m) ∧
      ∀ᶠ z in 𝓝 (x₀, t₀),
        u z.2 ≠ 0 ∧ f z = (f z / u z.2) * u z.2 := by
  have hbase : AnalyticAt ℝ (fun t => f (x₀, t)) t₀ :=
    hf.comp (analyticAt_const.prod analyticAt_id)
  obtain ⟨u, hu, hu0, heq⟩ := exists_analytic_unit_of_iteratedDeriv hbase hzero hm
  have hunit : ∀ᶠ t in 𝓝 t₀, u t ≠ 0 := hu.continuousAt.eventually_ne hu0
  refine ⟨u, hu, hu0, analyticAt_div_vertical_unit hf hu hu0, ?_, ?_⟩
  · filter_upwards [heq, hunit] with t ht hn
    exact ⟨ht, by rw [ht, mul_div_cancel_right₀ _ hn]⟩
  · filter_upwards [continuous_snd.continuousAt.eventually hunit] with z hz
    exact ⟨hz, (div_mul_cancel₀ _ hz).symm⟩

/-- The normalization is valid on an actual nonempty product neighborhood.
Its scalar unit is analytic and nonvanishing throughout the vertical
neighborhood, and the normalized function is jointly analytic throughout the
product. -/
theorem exists_analytic_weierstrass_normalization_on
    (f : E × ℝ → ℝ) (x₀ : E) (t₀ : ℝ) (m : ℕ)
    (hf : AnalyticAt ℝ f (x₀, t₀))
    (hzero : ∀ j < m, iteratedDeriv j (fun t => f (x₀, t)) t₀ = 0)
    (hm : iteratedDeriv m (fun t => f (x₀, t)) t₀ ≠ 0) :
    ∃ (U : Set E) (V : Set ℝ) (u : ℝ → ℝ),
      IsOpen U ∧ x₀ ∈ U ∧ IsOpen V ∧ t₀ ∈ V ∧
      AnalyticOnNhd ℝ u V ∧ (∀ t ∈ V, u t ≠ 0) ∧
      AnalyticOnNhd ℝ (fun z : E × ℝ => f z / u z.2) (U ×ˢ V) ∧
      (∀ t ∈ V, f (x₀, t) = (t - t₀) ^ m * u t ∧
        f (x₀, t) / u t = (t - t₀) ^ m) ∧
      ∀ z ∈ U ×ˢ V, f z = (f z / u z.2) * u z.2 := by
  obtain ⟨u, hu, _, hF, hbase, hjoint⟩ :=
    exists_analytic_weierstrass_normalization f x₀ t₀ m hf hzero hm
  have hall : {z : E × ℝ |
      AnalyticAt ℝ u z.2 ∧
      AnalyticAt ℝ (fun w : E × ℝ => f w / u w.2) z ∧
      (f (x₀, z.2) = (z.2 - t₀) ^ m * u z.2 ∧
        f (x₀, z.2) / u z.2 = (z.2 - t₀) ^ m) ∧
      u z.2 ≠ 0 ∧ f z = (f z / u z.2) * u z.2} ∈ 𝓝 (x₀, t₀) := by
    filter_upwards [continuous_snd.continuousAt.eventually hu.eventually_analyticAt,
      hF.eventually_analyticAt, continuous_snd.continuousAt.eventually hbase, hjoint]
      with z hzu hzF hzb hzj
    exact ⟨hzu, hzF, hzb, hzj⟩
  obtain ⟨U, V, hU, hxU, hV, htV, hUV⟩ := mem_nhds_prod_iff'.mp hall
  refine ⟨U, V, u, hU, hxU, hV, htV, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact (hUV (show (x₀, t) ∈ U ×ˢ V from ⟨hxU, ht⟩)).1
  · intro t ht
    exact (hUV (show (x₀, t) ∈ U ×ˢ V from ⟨hxU, ht⟩)).2.2.2.1
  · intro z hz
    exact (hUV hz).2.1
  · intro t ht
    exact (hUV (show (x₀, t) ∈ U ×ˢ V from ⟨hxU, ht⟩)).2.2.1
  · intro z hz
    exact (hUV hz).2.2.2.2

end PlanarNikodym
