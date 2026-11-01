import PlanarNikodym.Analysis.Fourier.LinearConeAmplitudeL2
import PlanarNikodym.Analysis.Fourier.UniformAmplitudeFourier
import PlanarNikodym.Analysis.Fourier.TimeLocalizedIntegrability

/-! The output square sum for true variable-amplitude cone integrals.
One actual Fourier-coefficient constant controls every time slice. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

theorem sum_lintegral_amplitudeCone_timeLocalized_sq_le
    (S : ℕ → SchwartzMap (Plane × Plane) ℂ) {h : Plane → ℂ}
    (hh : StronglyMeasurable h) (h2 : MemLp h 2) (b δ : ℝ) (N : ℕ)
    (h1 : ∀ i : ℕ, Integrable (timeLocalizedData b δ i h))
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hgap : ∀ x : Plane, |x.2| < a → h x = 0)
    (L : ℝ≥0∞) (hL : ∀ i : ℕ,
      (∫⁻ ζ : AmplitudeFourierSpace, ‖jointAmplitudeFourier (S i) ζ‖ₑ) ≤ L) :
    (∑ i ∈ Finset.range N, ∫⁻ w : Plane,
      ‖amplitudeConeExtension (fun w x => S i (w, x)) (timeLocalizedData b δ i h) r w‖ₑ ^
        (2 : ℕ)) ≤
      (L ^ (2 : ℕ) * ENNReal.ofReal (a⁻¹ * r⁻¹ ^ (2 : ℕ))) *
        ∫⁻ x : Plane, ‖h x‖ₑ ^ (2 : ℕ) := by
  have hi (i : ℕ) : (∫⁻ w : Plane,
      ‖amplitudeConeExtension (fun w x => S i (w, x)) (timeLocalizedData b δ i h) r w‖ₑ ^
        (2 : ℕ)) ≤
      (L ^ (2 : ℕ) * ENNReal.ofReal (a⁻¹ * r⁻¹ ^ (2 : ℕ))) *
        ∫⁻ x : Plane, ‖timeLocalizedData b δ i h x‖ₑ ^ (2 : ℕ) := by
    have hlocalgap : ∀ x : Plane, |x.2| < a → timeLocalizedData b δ i h x = 0 := by
      intro x hx
      simp only [timeLocalizedData, hgap x hx, mul_zero]
    calc
      _ ≤ (∫⁻ ζ : AmplitudeFourierSpace, ‖jointAmplitudeFourier (S i) ζ‖ₑ) ^ (2 : ℕ) *
          (ENNReal.ofReal (a⁻¹ * r⁻¹ ^ (2 : ℕ)) *
            ∫⁻ x : Plane, ‖timeLocalizedData b δ i h x‖ₑ ^ (2 : ℕ)) :=
        lintegral_amplitudeConeExtension_sq_le (S i) _
          (stronglyMeasurable_timeLocalizedData b δ i hh).measurable
          (h1 i) (memLp_timeLocalizedData_two b δ i h2) ha hr hlocalgap
      _ ≤ L ^ (2 : ℕ) * (ENNReal.ofReal (a⁻¹ * r⁻¹ ^ (2 : ℕ)) *
          ∫⁻ x : Plane, ‖timeLocalizedData b δ i h x‖ₑ ^ (2 : ℕ)) :=
        mul_le_mul_left (pow_le_pow_left' (hL i) 2) _
      _ = _ := (mul_assoc _ _ _).symm
  calc
    _ ≤ ∑ i ∈ Finset.range N,
        (L ^ (2 : ℕ) * ENNReal.ofReal (a⁻¹ * r⁻¹ ^ (2 : ℕ))) *
          ∫⁻ x : Plane, ‖timeLocalizedData b δ i h x‖ₑ ^ (2 : ℕ) :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = (L ^ (2 : ℕ) * ENNReal.ofReal (a⁻¹ * r⁻¹ ^ (2 : ℕ))) *
        ∑ i ∈ Finset.range N, ∫⁻ x : Plane, ‖timeLocalizedData b δ i h x‖ₑ ^ (2 : ℕ) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_right (sum_lintegral_timeLocalizedData_sq_le b δ N hh) _

/-- The same output square sum for the actual compact-symbol partial
Fourier data, including the original two-dimensional input dilation. -/
theorem sum_lintegral_amplitudeCone_weightedPartial_sq_le
    (S : ℕ → SchwartzMap (Plane × Plane) ℂ) (b : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (N : ℕ) {m : Plane → ℝ} (hm : Continuous m) (hc : HasCompactSupport m)
    {f : Plane → ℂ} (h1 : Integrable f) (h2 : MemLp f 2) {a r M : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hbound : ∀ ξ : Plane, |m ξ| ≤ M)
    (hgap : ∀ ξ : Plane, |ξ.2| < a → m ξ = 0)
    (L : ℝ≥0∞) (hL : ∀ i : ℕ,
      (∫⁻ ζ : AmplitudeFourierSpace, ‖jointAmplitudeFourier (S i) ζ‖ₑ) ≤ L) :
    (∑ i ∈ Finset.range N, ∫⁻ w : Plane,
      ‖amplitudeConeExtension (fun w x => S i (w, x))
        (timeLocalizedData b δ i (fun y => weightedPartialFourierData m f r y.1 y.2)) r w‖ₑ ^
          (2 : ℕ)) ≤
      (L ^ (2 : ℕ) * ENNReal.ofReal (a⁻¹ * r⁻¹ ^ (2 : ℕ))) *
        (ENNReal.ofReal (M ^ (2 : ℕ) * r⁻¹ ^ (3 : ℕ)) *
          ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ)) := by
  calc
    _ ≤ (L ^ (2 : ℕ) * ENNReal.ofReal (a⁻¹ * r⁻¹ ^ (2 : ℕ))) *
        ∫⁻ x : Plane, ‖weightedPartialFourierData m f r x.1 x.2‖ₑ ^ (2 : ℕ) :=
      sum_lintegral_amplitudeCone_timeLocalized_sq_le S
        (stronglyMeasurable_partialFourierData (weighted_scaledFourierData_continuous hm h1 r) r)
        (memLp_weightedPartialFourierData_two hm hc h1 hr) b δ N
        (fun i => integrable_timeLocalized_weightedPartialFourierData b hδ i hm hc h1 hr)
        ha hr (fun x hx => weightedPartialFourierData_eq_zero_of_gap hgap r x.1 x.2 hx) L hL
    _ ≤ _ := mul_le_mul_right
      (lintegral_weightedPartialFourierData_sq_le_of_integrable hm hc h1 h2 hr hbound) _

/-- Fixed compact amplitude support and full jet bounds actually produce
constants before every input, scale, window count and parameter choice. -/
theorem exists_uniform_amplitudeCone_weightedPartial_square_sum_bound
    {P : Type*} (S : P → SchwartzMap (Plane × Plane) ℂ)
    {K : Set (Plane × Plane)} (hK : IsCompact K)
    (hs : ∀ p, tsupport (S p) ⊆ K)
    (hjet : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p x, ‖iteratedFDeriv ℝ n (S p) x‖ ≤ B)
    {m : Plane → ℝ} (hm : Continuous m) (hc : HasCompactSupport m) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧
      ∀ (π : ℕ → P) (f : Plane → ℂ), Integrable f → MemLp f 2 →
      ∀ (a r b δ : ℝ) (N : ℕ), 0 < a → 0 < r → 0 < δ →
      (∀ ξ : Plane, |ξ.2| < a → m ξ = 0) →
      (∑ i ∈ Finset.range N, ∫⁻ w : Plane,
        ‖amplitudeConeExtension (fun w x => S (π i) (w, x))
          (timeLocalizedData b δ i (fun y => weightedPartialFourierData m f r y.1 y.2)) r w‖ₑ ^
            (2 : ℕ)) ≤
        ENNReal.ofReal (C ^ (2 : ℕ) * (a⁻¹ * r⁻¹ ^ (2 : ℕ))) *
          (ENNReal.ofReal (M ^ (2 : ℕ) * r⁻¹ ^ (3 : ℕ)) *
            ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ)) := by
  obtain ⟨C, hC, hFourier⟩ := exists_uniform_jointAmplitudeFourier_L1_bound S hK hs hjet
  obtain ⟨ξ₀, hξ₀⟩ := hm.norm.exists_forall_ge_of_hasCompactSupport hc.norm
  refine ⟨C, ‖m ξ₀‖, hC, norm_nonneg _, ?_⟩
  intro π f h1 h2 a r b δ N ha hr hδ hgap
  have he := sum_lintegral_amplitudeCone_weightedPartial_sq_le (M := ‖m ξ₀‖)
    (fun i => S (π i)) b hδ N
    hm hc h1 h2 ha hr (fun ξ => by simpa only [Real.norm_eq_abs] using hξ₀ ξ)
    hgap (ENNReal.ofReal C) (fun i => hFourier (π i))
  simpa only [← ENNReal.ofReal_pow hC, ← ENNReal.ofReal_mul (sq_nonneg C)] using he

end PlanarNikodym
