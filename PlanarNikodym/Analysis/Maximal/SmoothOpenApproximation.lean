import PlanarNikodym.Analysis.Maximal.DyadicSummation
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Smooth monotone approximation of open indicators, evaluated on the
actual curves. This provides the approximation step used in the paper's
exclusion argument without requiring Fourier reconstruction of indicators. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal ContDiff
namespace PlanarNikodym

/-- Concrete smooth approximants; their existence is proved below.
Compact support is not asserted for an unbounded open set. -/
structure OpenSmoothApproximation (O : Set Plane) where
  fn : ℕ → Plane → ℝ
  smooth : ∀ n, ContDiff ℝ ∞ (fn n)
  nonnegative : ∀ n x, 0 ≤ fn n x
  le_one : ∀ n x, fn n x ≤ 1
  zero_outside : ∀ n x, x ∉ O → fn n x = 0
  monotone : Monotone fn
  supremum : ∀ x, (⨆ n, ENNReal.ofReal (fn n x)) = O.indicator (fun _ => 1) x

theorem exists_openSmoothApproximation (O : Set Plane) (hO : IsOpen O) :
    Nonempty (OpenSmoothApproximation O) := by
  obtain ⟨g, hgO, hgs, hgr⟩ := hO.exists_contDiff_support_eq (n := ⊤)
  have hg (x : Plane) : 0 ≤ g x ∧ g x ≤ 1 := hgr (mem_range_self x)
  let f : ℕ → Plane → ℝ := fun n x => 1 - (1 - g x) ^ (n + 1)
  have hnonneg (n : ℕ) (x : Plane) : 0 ≤ f n x := by
    have hp : (1 - g x) ^ (n + 1) ≤ 1 :=
      pow_le_one₀ (by linarith [(hg x).2]) (by linarith [(hg x).1])
    dsimp [f]
    linarith
  have hmono : Monotone f := by
    apply monotone_nat_of_le_succ
    intro n x
    have hp := pow_nonneg (by linarith [(hg x).2] : 0 ≤ 1 - g x) (n + 1)
    change 1 - (1 - g x) ^ (n + 1) ≤ 1 - (1 - g x) ^ ((n + 1) + 1)
    rw [pow_succ (1 - g x) (n + 1)]
    nlinarith [(hg x).1]
  refine ⟨{
    fn := f
    smooth := fun n => contDiff_const.sub ((contDiff_const.sub hgs).pow (n + 1))
    nonnegative := hnonneg
    le_one := ?_
    zero_outside := ?_
    monotone := hmono
    supremum := ?_ }⟩
  · intro n x
    have hp := pow_nonneg (by linarith [(hg x).2] : 0 ≤ 1 - g x) (n + 1)
    dsimp [f]
    linarith
  · intro n x hx
    have hz : g x = 0 := by
      have : x ∉ Function.support g := hgO ▸ hx
      simpa only [Function.mem_support, not_not] using this
    simp [f, hz]
  · intro x
    apply iSup_eq_of_tendsto (fun n m hnm => ENNReal.ofReal_le_ofReal (hmono hnm x))
    by_cases hx : x ∈ O
    · have hgp : 0 < g x := lt_of_le_of_ne (hg x).1 (Ne.symm (by
        have : x ∈ Function.support g := hgO ▸ hx
        exact this))
      have ht : Tendsto (fun n : ℕ => (1 - g x) ^ (n + 1)) atTop (𝓝 (0 : ℝ)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one
          (by linarith [(hg x).2]) (by linarith)).comp (tendsto_add_atTop_nat 1)
      have hf : Tendsto (fun n => f n x) atTop (𝓝 (1 : ℝ)) := by
        simpa only [f, sub_zero] using tendsto_const_nhds.sub ht
      simpa [hx, Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hf
    · have hz : g x = 0 := by
        have : x ∉ Function.support g := hgO ▸ hx
        simpa only [Function.mem_support, not_not] using this
      simp only [f, hz, sub_zero, one_pow, sub_self, ENNReal.ofReal_zero,
        indicator_of_notMem hx]
      exact tendsto_const_nhds

namespace OpenSmoothApproximation
variable {O : Set Plane} (A : OpenSmoothApproximation O)

def enn (n : ℕ) (x : Plane) : ℝ≥0∞ := ENNReal.ofReal (A.fn n x)

theorem measurable_enn (n : ℕ) : Measurable (A.enn n) :=
  ENNReal.continuous_ofReal.measurable.comp (A.smooth n).continuous.measurable

theorem monotone_enn : Monotone A.enn :=
  fun _ _ hnm x => ENNReal.ofReal_le_ofReal (A.monotone hnm x)

theorem complex_norm_le_indicator (n : ℕ) (x : Plane) :
    ‖(A.fn n x : ℂ)‖ ≤ O.indicator (fun _ => (1 : ℝ)) x := by
  rw [Complex.norm_real, Real.norm_of_nonneg (A.nonnegative n x)]
  by_cases hx : x ∈ O
  · simpa [hx] using A.le_one n x
  · simp [hx, A.zero_outside n x hx]

theorem integrable_complex (hO : MeasurableSet O) (hOf : volume O < ⊤) (n : ℕ) :
    Integrable (fun x => (A.fn n x : ℂ)) := by
  have hdom : Integrable (O.indicator (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff hO).mpr (integrableOn_const hOf.ne)
  exact hdom.mono' (Complex.continuous_ofReal.comp (A.smooth n).continuous).aestronglyMeasurable
    (ae_of_all _ (A.complex_norm_le_indicator n))

theorem memLp_complex (hO : MeasurableSet O) (hOf : volume O < ⊤)
    (p : ℝ≥0) (n : ℕ) : MemLp (fun x => (A.fn n x : ℂ)) p volume := by
  have hdom : MemLp (O.indicator (fun _ => (1 : ℝ))) p volume :=
    memLp_indicator_const p hO 1 (Or.inr hOf.ne)
  exact hdom.mono' (Complex.continuous_ofReal.comp (A.smooth n).continuous).aestronglyMeasurable
    (ae_of_all _ (A.complex_norm_le_indicator n))

theorem eLpNorm_complex_le (hO : MeasurableSet O) {p : ℝ≥0} (hp : 0 < p) (n : ℕ) :
    eLpNorm (fun x => (A.fn n x : ℂ)) p volume ≤ volume O ^ (1 / (p : ℝ)) := by
  calc
    _ ≤ eLpNorm (O.indicator (fun _ => (1 : ℂ))) p volume := by
      apply eLpNorm_mono
      intro x
      simpa only [norm_indicator_eq_indicator_norm, norm_one] using
        A.complex_norm_le_indicator n x
    _ = _ := by
      simp [eLpNorm_indicator_const hO (by exact_mod_cast hp.ne' : (p : ℝ≥0∞) ≠ 0)
        ENNReal.coe_ne_top]

end OpenSmoothApproximation

namespace Family
variable {d : ℕ} (G : Family 2 d)

/-- Monotone convergence on the restricted time interval; no regularity of
the ambient extension of gamma outside I is required. -/
theorem positiveAverage_iSup_restrict (f : ℕ → Plane → ℝ≥0∞)
    (p : Parameters 2 d)
    (hm : ∀ n, AEMeasurable (fun t => f n (G.graphMap p t))
      (volume.restrict G.I.carrier)) (hmono : Monotone f) :
    G.positiveAverage (fun x => ⨆ n, f n x) p = ⨆ n, G.positiveAverage (f n) p :=
  lintegral_iSup' hm (ae_of_all _ (fun t _ _ hij => hmono hij (G.graphMap p t)))

theorem positiveMaximal_iSup_restrict (U : Set (Parameters 2 d))
    (f : ℕ → Plane → ℝ≥0∞)
    (hm : ∀ p ∈ U, ∀ n, AEMeasurable (fun t => f n (G.graphMap p t))
      (volume.restrict G.I.carrier)) (hmono : Monotone f) :
    G.positiveMaximal U (fun x => ⨆ n, f n x) =
      fun z => ⨆ n, G.positiveMaximal U (f n) z := by
  ext z
  apply le_antisymm
  · apply iSup_le
    intro u
    apply iSup_le
    intro hu
    rw [G.positiveAverage_iSup_restrict f (z, u) (hm _ hu) hmono]
    exact iSup_le fun n => le_iSup_of_le n
      (G.positiveAverage_le_maximal (U := U) (f n) hu)
  · apply iSup_le
    intro n
    exact G.positiveMaximal_mono (U := U) Subset.rfl
      (fun x => le_iSup (fun m => f m x) n) z

/-- The open-set maximal function is exactly the pointwise increasing
supremum of the maximal functions of actual smooth nonnegative tests. -/
theorem positiveMaximal_open_eq_iSup_smooth {O : Set Plane}
    (A : OpenSmoothApproximation O) (U : Set (Parameters 2 d))
    (hU : U ⊆ G.W) (hs : G.IsSmooth) :
    G.positiveMaximal U (O.indicator (fun _ => 1)) =
      fun z => ⨆ n, G.positiveMaximal U (A.enn n) z := by
  have he : O.indicator (fun _ => (1 : ℝ≥0∞)) = fun x => ⨆ n, A.enn n x :=
    funext (fun x => (A.supremum x).symm)
  rw [he]
  apply G.positiveMaximal_iSup_restrict U A.enn _ A.monotone_enn
  intro p hp n
  obtain ⟨K, hK⟩ := G.smooth_graph_lipschitz hs p (hU hp)
  exact ((ENNReal.continuous_ofReal.comp (A.smooth n).continuous).comp_continuousOn
    hK.continuousOn).aemeasurable measurableSet_Icc

/-- A finite-exponent maximal estimate on bounded nonnegative smooth tests
suffices for the open-set estimate used to exclude Nikodym sets. In
particular, no direct Fourier reconstruction of open indicators is needed.
The analytic estimate on smooth tests is an explicit hypothesis here. -/
theorem openMaximalEstimate_of_smooth_tests (U : Set (Parameters 2 d))
    (hU : U ⊆ G.W) (hs : G.IsSmooth) (p : ℝ≥0) (hp : 1 ≤ p) (C : ℝ≥0)
    (htest : ∀ f : Plane → ℝ, ContDiff ℝ ∞ f → (∀ x, 0 ≤ f x) →
      (∀ x, f x ≤ 1) → Integrable (fun x => (f x : ℂ)) →
      MemLp (fun x => (f x : ℂ)) p volume →
      Measurable (G.positiveMaximal U (fun x => ENNReal.ofReal (f x))) ∧
      eLpNorm (G.positiveMaximal U (fun x => ENNReal.ofReal (f x))) p volume ≤
        C * eLpNorm (fun x => (f x : ℂ)) p volume) :
    G.OpenMaximalEstimate U := by
  refine ⟨p, hp, C, ?_⟩
  intro O hO hOf
  obtain ⟨A⟩ := exists_openSmoothApproximation O hO
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have htestA (n : ℕ) := htest (A.fn n) (A.smooth n) (A.nonnegative n)
    (A.le_one n) (A.integrable_complex hO.measurableSet hOf n)
    (A.memLp_complex hO.measurableSet hOf p n)
  have hm (n : ℕ) : Measurable (G.positiveMaximal U (A.enn n)) := (htestA n).1
  have hmono : Monotone (fun n => G.positiveMaximal U (A.enn n)) :=
    fun _ _ hnm => G.positiveMaximal_mono Subset.rfl (A.monotone_enn hnm)
  rw [G.positiveMaximal_open_eq_iSup_smooth A U hU hs]
  refine ⟨Measurable.iSup hm, ?_⟩
  rw [eLpNorm_iSup_nonnegative volume p hp0 _ hm hmono]
  apply iSup_le
  intro n
  exact (htestA n).2.trans (mul_le_mul_right (A.eLpNorm_complex_le hO.measurableSet hp0 n) C)

end Family
end PlanarNikodym
