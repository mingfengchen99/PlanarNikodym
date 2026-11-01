import PlanarNikodym.Geometry.AnalyticDivisionSeries
import PlanarNikodym.Geometry.AnalyticImplicit
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Analytic division by a graph and preparation at a simple root

The unit in the factorization is constructed from a genuinely convergent parameter-dependent
Hadamard quotient. This proves preparation of degree one. It does not assert preparation at
multiple roots or analytic cell decomposition.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace PlanarNikodym

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Joint analytic division by the equation of an analytic graph. -/
theorem exists_analytic_graph_quotient
    (f : E × ℝ → F) (h : E → ℝ) (x₀ : E)
    (hf : AnalyticAt ℝ f (x₀, h x₀)) (hh : AnalyticAt ℝ h x₀) :
    ∃ q : E × ℝ → F, AnalyticAt ℝ q (x₀, h x₀) ∧
      ∀ᶠ z in 𝓝 (x₀, h x₀),
        f z - f (z.1, h z.1) = (z.2 - h z.1) • q z := by
  let shift : E × ℝ → E × ℝ := fun z => (z.1, z.2 + h z.1)
  let unshift : E × ℝ → E × ℝ := fun z => (z.1, z.2 - h z.1)
  have hs : AnalyticAt ℝ shift (x₀, 0) :=
    analyticAt_fst.prod (analyticAt_snd.add (hh.comp analyticAt_fst))
  have hu : AnalyticAt ℝ unshift (x₀, h x₀) :=
    analyticAt_fst.prod (analyticAt_snd.sub (hh.comp analyticAt_fst))
  have hfs : AnalyticAt ℝ (fun z => f (shift z)) (x₀, 0) := by
    apply AnalyticAt.comp _ hs
    simpa only [shift, zero_add] using hf
  obtain ⟨q, hq, heq⟩ :=
    exists_analytic_coordinate_quotient (fun z => f (shift z)) x₀ 0 hfs
  refine ⟨fun z => q (unshift z), ?_, ?_⟩
  · apply AnalyticAt.comp _ hu
    simpa only [unshift, sub_self] using hq
  · have ht : Tendsto unshift (𝓝 (x₀, h x₀)) (𝓝 (x₀, 0)) := by
      simpa only [unshift, sub_self] using hu.continuousAt.tendsto
    filter_upwards [ht.eventually heq] with z hz
    simpa only [shift, unshift, sub_add_cancel, zero_add, sub_zero] using hz

/-- A function vanishing along an analytic graph is analytically divisible by its equation. -/
theorem exists_analytic_graph_factor
    (f : E × ℝ → F) (h : E → ℝ) (x₀ : E)
    (hf : AnalyticAt ℝ f (x₀, h x₀)) (hh : AnalyticAt ℝ h x₀)
    (hz : ∀ᶠ x in 𝓝 x₀, f (x, h x) = 0) :
    ∃ q : E × ℝ → F, AnalyticAt ℝ q (x₀, h x₀) ∧
      ∀ᶠ z in 𝓝 (x₀, h x₀), f z = (z.2 - h z.1) • q z := by
  obtain ⟨q, hq, heq⟩ := exists_analytic_graph_quotient f h x₀ hf hh
  refine ⟨q, hq, ?_⟩
  filter_upwards [heq, continuous_fst.continuousAt.eventually hz] with z he hz
  simpa only [hz, sub_zero] using he

/-- The analytic factor at a root is the actual derivative in the distinguished direction. -/
theorem analytic_graph_factor_value
    (f q : E × ℝ → ℝ) (h : E → ℝ) (x₀ : E)
    (hq : AnalyticAt ℝ q (x₀, h x₀))
    (heq : ∀ᶠ z in 𝓝 (x₀, h x₀), f z = (z.2 - h z.1) * q z) :
    q (x₀, h x₀) = deriv (fun t => f (x₀, t)) (h x₀) := by
  have ht : AnalyticAt ℝ (fun t : ℝ => (x₀, t)) (h x₀) :=
    analyticAt_const.prod analyticAt_id
  have hqd := (hq.comp ht).differentiableAt.hasDerivAt
  have hd : HasDerivAt
      (fun t : ℝ => (t - h x₀) * q (x₀, t)) (q (x₀, h x₀)) (h x₀) := by
    convert! ((hasDerivAt_id (h x₀)).sub_const (h x₀)).mul hqd using 1
    simp [Function.comp_def]
  exact (hd.congr_of_eventuallyEq (ht.continuousAt.eventually heq)).deriv.symm

variable [CompleteSpace E]

/-- Analytic preparation at a simple real root. Both the root and the unit are constructed,
the unit is nonzero on a neighborhood, and its value is the actual vertical derivative. -/
theorem exists_analytic_simple_root_preparation
    (f : E × ℝ → ℝ) (x₀ : E) (t₀ : ℝ)
    (hf : AnalyticAt ℝ f (x₀, t₀)) (hf0 : f (x₀, t₀) = 0)
    (hd : deriv (fun t => f (x₀, t)) t₀ ≠ 0) :
    ∃ h : E → ℝ, ∃ u : E × ℝ → ℝ,
      AnalyticAt ℝ h x₀ ∧ h x₀ = t₀ ∧ AnalyticAt ℝ u (x₀, t₀) ∧
      u (x₀, t₀) = deriv (fun t => f (x₀, t)) t₀ ∧
      (∀ᶠ z in 𝓝 (x₀, t₀), u z ≠ 0 ∧ f z = (z.2 - h z.1) * u z) := by
  have hi : ((fderiv ℝ f (x₀, t₀)).comp (ContinuousLinearMap.inr ℝ E ℝ)).IsInvertible := by
    rw [← fderiv_snd_slice f (x₀, t₀) hf.differentiableAt]
    refine ⟨(LinearEquiv.smulOfNeZero ℝ ℝ
      (deriv (fun t => f (x₀, t)) t₀) hd).toContinuousLinearEquiv, ?_⟩
    ext
    simp
  obtain ⟨h, hh, hh0, hzero, _⟩ := exists_analytic_implicit f x₀ t₀ hf hf0 hi
  have hfh : AnalyticAt ℝ f (x₀, h x₀) := by simpa only [hh0] using hf
  obtain ⟨u, hu, heq⟩ := exists_analytic_graph_factor f h x₀ hfh hh hzero
  have heq' : ∀ᶠ z in 𝓝 (x₀, h x₀), f z = (z.2 - h z.1) * u z := by
    simpa only [smul_eq_mul] using heq
  have hv := analytic_graph_factor_value f u h x₀ hu heq'
  rw [hh0] at hu hv heq'
  refine ⟨h, u, hh, hh0, hu, hv, ?_⟩
  filter_upwards [hu.continuousAt.eventually_ne (hv.trans_ne hd), heq'] with z hz he
  exact ⟨hz, he⟩

/-- The simple-root preparation holds on an actual product neighborhood. The root stays
inside the vertical neighborhood and the factor is analytic and nonzero everywhere there. -/
theorem exists_analytic_simple_root_preparation_on
    (f : E × ℝ → ℝ) (x₀ : E) (t₀ : ℝ)
    (hf : AnalyticAt ℝ f (x₀, t₀)) (hf0 : f (x₀, t₀) = 0)
    (hd : deriv (fun t => f (x₀, t)) t₀ ≠ 0) :
    ∃ (U : Set E) (V : Set ℝ) (h : E → ℝ) (u : E × ℝ → ℝ),
      IsOpen U ∧ x₀ ∈ U ∧ IsOpen V ∧ t₀ ∈ V ∧
      h x₀ = t₀ ∧ MapsTo h U V ∧
      AnalyticOnNhd ℝ h U ∧ AnalyticOnNhd ℝ u (U ×ˢ V) ∧
      ∀ z ∈ U ×ˢ V, u z ≠ 0 ∧ f z = (z.2 - h z.1) * u z := by
  obtain ⟨h, u, hh, hh0, hu, _, heq⟩ :=
    exists_analytic_simple_root_preparation f x₀ t₀ hf hf0 hd
  have hall : {z : E × ℝ | AnalyticAt ℝ h z.1 ∧ AnalyticAt ℝ u z ∧
      u z ≠ 0 ∧ f z = (z.2 - h z.1) * u z} ∈ 𝓝 (x₀, t₀) := by
    filter_upwards [continuous_fst.continuousAt.eventually hh.eventually_analyticAt,
      hu.eventually_analyticAt, heq] with z hz1 hz2 hz3
    exact ⟨hz1, hz2, hz3⟩
  obtain ⟨U, V, hU, hxU, hV, htV, hUV⟩ := mem_nhds_prod_iff'.mp hall
  have hpre : h ⁻¹' V ∈ 𝓝 x₀ :=
    hh.continuousAt.preimage_mem_nhds (by simpa only [hh0] using hV.mem_nhds htV)
  obtain ⟨U', hU'sub, hU', hxU'⟩ :=
    mem_nhds_iff.mp (inter_mem (hU.mem_nhds hxU) hpre)
  refine ⟨U', V, h, u, hU', hxU', hV, htV, hh0,
    fun x hx => (hU'sub hx).2, ?_, ?_, ?_⟩
  · intro x hx
    exact (hUV (show (x, t₀) ∈ U ×ˢ V from ⟨(hU'sub hx).1, htV⟩)).1
  · intro z hz
    exact (hUV ⟨(hU'sub hz.1).1, hz.2⟩).2.1
  · intro z hz
    exact (hUV ⟨(hU'sub hz.1).1, hz.2⟩).2.2

/-- Actual analytic division by a function with a simple vertical zero: the remainder depends
only on the parameter, and equals the numerator restricted to the constructed root graph. -/
theorem exists_analytic_simple_root_division
    (f g : E × ℝ → ℝ) (x₀ : E) (t₀ : ℝ)
    (hf : AnalyticAt ℝ f (x₀, t₀)) (hg : AnalyticAt ℝ g (x₀, t₀))
    (hf0 : f (x₀, t₀) = 0) (hd : deriv (fun t => f (x₀, t)) t₀ ≠ 0) :
    ∃ (h : E → ℝ) (q : E × ℝ → ℝ) (r : E → ℝ),
      AnalyticAt ℝ h x₀ ∧ h x₀ = t₀ ∧
      AnalyticAt ℝ q (x₀, t₀) ∧ AnalyticAt ℝ r x₀ ∧
      (∀ x, r x = g (x, h x)) ∧
      (∀ᶠ z in 𝓝 (x₀, t₀), g z = q z * f z + r z.1) ∧
      (∀ᶠ z in 𝓝 (x₀, t₀), f z = 0 ↔ z.2 = h z.1) := by
  obtain ⟨h, u, hh, hh0, hu, hv, hfactor⟩ :=
    exists_analytic_simple_root_preparation f x₀ t₀ hf hf0 hd
  have hgh : AnalyticAt ℝ g (x₀, h x₀) := by simpa only [hh0] using hg
  obtain ⟨q₀, hq₀, heq⟩ := exists_analytic_graph_quotient g h x₀ hgh hh
  rw [hh0] at hq₀ heq
  have hun : u (x₀, t₀) ≠ 0 := hv.trans_ne hd
  refine ⟨h, fun z => q₀ z / u z, fun x => g (x, h x),
    hh, hh0, hq₀.div hu hun, ?_, fun _ => rfl, ?_, ?_⟩
  · exact hgh.comp (f := fun x : E => (x, h x)) (analyticAt_id.prod hh)
  · filter_upwards [hfactor, heq] with z hfz hez
    simp only [smul_eq_mul] at hez
    rw [hfz.2]
    have hc : q₀ z / u z * ((z.2 - h z.1) * u z) = (z.2 - h z.1) * q₀ z := by
      field_simp [hfz.1]
    rw [hc]
    exact (sub_eq_iff_eq_add.mp hez)
  · filter_upwards [hfactor] with z hz
    rw [hz.2, mul_eq_zero, or_iff_left hz.1, sub_eq_zero]

end PlanarNikodym
