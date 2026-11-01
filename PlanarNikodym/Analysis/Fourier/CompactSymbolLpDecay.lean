import PlanarNikodym.Analysis.Fourier.CompactSymbolOperator
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Compact parameter support turns pointwise Holder bounds for actual
scaled Fourier operators into Lp operator decay. The constants come from
actual compact symbol derivative bounds and the finite parameter volume. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff

namespace PlanarNikodym

/-- An extended-real pointwise bound on a fixed finite-measure support gives
an Lp bound without converting a possibly infinite input norm to a real. -/
theorem eLpNorm_le_finite_support_enorm_bound
    {P : Type*} [MeasurableSpace P] (μ : Measure P) {H : Set P} (hH : μ H ≠ (∞ : ℝ≥0∞))
    {F : P → ℂ} (B : ℝ) (hB : 0 ≤ B) (A : ℝ≥0∞) (p : ℝ≥0∞)
    (hbound : ∀ x, ‖F x‖ₑ ≤ ENNReal.ofReal B * A)
    (hs : ∀ x ∉ H, F x = 0) :
    eLpNorm F p μ ≤
      ENNReal.ofReal (B * (μ H).toReal ^ (1 / p.toReal)) * A := by
  classical
  let g : P → ℝ≥0∞ := H.indicator (fun _ => ENNReal.ofReal B * A)
  have hmono : ∀ x, ‖F x‖ₑ ≤ ‖g x‖ₑ := by
    intro x
    by_cases hx : x ∈ H
    · simpa only [g, indicator_of_mem hx, enorm_eq_self] using hbound x
    · simp only [hs x hx, enorm_zero, g, indicator_of_notMem hx, le_refl]
  have hweight : (μ H) ^ (1 / p.toReal) =
      ENNReal.ofReal ((μ H).toReal ^ (1 / p.toReal)) := by
    rw [ENNReal.toReal_rpow, ENNReal.ofReal_toReal
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) hH).ne]
  calc
    _ ≤ eLpNorm g p μ := eLpNorm_mono_enorm hmono
    _ ≤ (ENNReal.ofReal B * A) * (μ H) ^ (1 / p.toReal) := by
      simpa only [g, enorm_eq_self] using
        (eLpNorm_indicator_const_le (μ := μ) (s := H) (ENNReal.ofReal B * A) p)
    _ = _ := by rw [hweight, ENNReal.ofReal_mul hB]; ac_rfl

theorem sq_mul_inverse_power_add_two (A : ℝ) {r : ℝ} (hr : r ≠ 0) (N : ℕ) :
    r ^ 2 * (A * (r⁻¹) ^ (N + 2)) = A * (r⁻¹) ^ N := by
  rw [pow_add]
  calc
    _ = (A * (r⁻¹) ^ N) * (r * r⁻¹) ^ 2 := by ring
    _ = _ := by rw [mul_inv_cancel₀ hr, one_pow, mul_one]

/-- The true two-dimensional frequency Jacobian is absorbed by requesting
two extra orders of the actual kernel decay. The bound is uniform in the
symbol parameter, frequency scale and L1 input. -/
theorem exists_uniform_scaledSymbolOperator_enorm_decay
    {P : Type*} (S : P → ℝ → SchwartzMap Plane ℂ)
    {K : Set Plane} (hK : IsCompact K) (hs : ∀ a r, tsupport (S a r) ⊆ K)
    (hdecay : ∀ j N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      ∀ ξ, ‖iteratedFDeriv ℝ j (S a r) ξ‖ ≤ C * (r⁻¹) ^ N)
    (p q : ℝ≥0∞) [ENNReal.HolderConjugate q p] (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r → ∀ f : Plane → ℂ, Integrable f →
      ‖scaledSymbolOperator (S a r) r f‖ₑ ≤
        ENNReal.ofReal (C * (r⁻¹) ^ N) * eLpNorm f p volume := by
  obtain ⟨C, hC, hkernel⟩ := exists_uniform_complex_symbol_kernel_Lp_decay S hK hs hdecay
    q (ENNReal.HolderConjugate.one_le q p) (N + 2)
  refine ⟨C, hC, ?_⟩
  intro a r hr f hf
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  calc
    _ ≤ ENNReal.ofReal (r ^ 2) * eLpNorm (planeInverseFourierSchwartzCLM (S a r)) q volume *
        eLpNorm f p volume := scaledSymbolOperator_enorm_le (S a r) hf hr
    _ ≤ ENNReal.ofReal (r ^ 2) * ENNReal.ofReal (C * (r⁻¹) ^ (N + 2)) *
        eLpNorm f p volume := by gcongr; exact hkernel a r hr
    _ = _ := by
      rw [← ENNReal.ofReal_mul (sq_nonneg r), sq_mul_inverse_power_add_two C hrpos.ne' N]

/-- Holder-dual form of the compact-parameter Lp assembly. Compactness of
H supplies its finite volume; no parameter-volume constant is an input. -/
theorem exists_compact_symbol_operator_Lp_decay_of_holder {d : ℕ}
    (S : Parameters 2 d → ℝ → SchwartzMap Plane ℂ)
    {K : Set Plane} (hK : IsCompact K) (hs : ∀ a r, tsupport (S a r) ⊆ K)
    (hdecay : ∀ j N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      ∀ ξ, ‖iteratedFDeriv ℝ j (S a r) ξ‖ ≤ C * (r⁻¹) ^ N)
    {H : Set (Parameters 2 d)} (hH : IsCompact H)
    (hparam : ∀ a ∉ H, ∀ r : ℝ, S a r = 0)
    (p q : ℝ≥0∞) [ENNReal.HolderConjugate q p] (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ f : Plane → ℂ, Integrable f →
      eLpNorm (fun a => scaledSymbolOperator (S a r) r f) p volume ≤
        ENNReal.ofReal (C * (r⁻¹) ^ N) * eLpNorm f p volume := by
  obtain ⟨B, hB, hpoint⟩ := exists_uniform_scaledSymbolOperator_enorm_decay S hK hs hdecay p q N
  let V : ℝ := (volume H).toReal ^ (1 / p.toReal)
  let C : ℝ := B * V
  have hV : 0 ≤ V := Real.rpow_nonneg ENNReal.toReal_nonneg _
  refine ⟨C, mul_nonneg hB hV, ?_⟩
  intro r hr f hf
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have hzero : ∀ a ∉ H, scaledSymbolOperator (S a r) r f = 0 := by
    intro a ha
    rw [hparam a ha r]
    simp [scaledSymbolOperator]
  have h := eLpNorm_le_finite_support_enorm_bound (volume : Measure (Parameters 2 d))
    hH.measure_ne_top (B * (r⁻¹) ^ N) (mul_nonneg hB (by positivity))
      (eLpNorm f p volume) p (fun a => hpoint a r hr f hf) hzero
  have he : (B * (r⁻¹) ^ N) * V = C * (r⁻¹) ^ N := by dsimp [C]; ring
  rw [he] at h
  exact h

/-- Every finite p ≥ 1, and also p = ∞, admits a Holder dual. Thus full-jet
rapid symbol decay on fixed compact frequency and parameter supports gives
arbitrary-order Lp decay for the actual scaled Fourier operator. -/
theorem exists_compact_symbol_operator_Lp_decay {d : ℕ}
    (S : Parameters 2 d → ℝ → SchwartzMap Plane ℂ)
    {K : Set Plane} (hK : IsCompact K) (hs : ∀ a r, tsupport (S a r) ⊆ K)
    (hdecay : ∀ j N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      ∀ ξ, ‖iteratedFDeriv ℝ j (S a r) ξ‖ ≤ C * (r⁻¹) ^ N)
    {H : Set (Parameters 2 d)} (hH : IsCompact H)
    (hparam : ∀ a ∉ H, ∀ r : ℝ, S a r = 0) (p : ℝ≥0∞) (hp : 1 ≤ p) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ f : Plane → ℂ, Integrable f →
      eLpNorm (fun a => scaledSymbolOperator (S a r) r f) p volume ≤
        ENNReal.ofReal (C * (r⁻¹) ^ N) * eLpNorm f p volume := by
  let q : ℝ≥0∞ := (1 - p⁻¹)⁻¹
  have hinv : p⁻¹ ≤ 1 := by simpa using ENNReal.inv_le_inv.mpr hp
  letI : ENNReal.HolderConjugate q p := by
    rw [ENNReal.holderConjugate_iff]
    dsimp only [q]
    rw [inv_inv]
    exact tsub_add_cancel_of_le hinv
  exact exists_compact_symbol_operator_Lp_decay_of_holder S hK hs hdecay hH hparam p q N

end PlanarNikodym
