import PlanarNikodym.Analysis.Fourier.GlyzL2Overlap
import Mathlib.Data.Int.Interval

/-! The degree-one GLYZ base case for actual Fourier-supported Schwartz
pieces. The bound is uniform in the interval scale and number of pieces. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform Classical ENNReal NNReal
namespace PlanarNikodym

def glyzLineFrequencyBox (δ : ℝ) (i : ℕ) : Set ℝ :=
  {ξ | |ξ / δ - ((i : ℝ) + 1 / 2)| ≤ 1}

theorem glyzLineFrequencyBox_eq_Icc {δ : ℝ} (hδ : 0 < δ) (i : ℕ) :
    glyzLineFrequencyBox δ i =
      Icc (δ * ((i : ℝ) + 1 / 2) - δ) (δ * ((i : ℝ) + 1 / 2) + δ) := by
  ext ξ
  simp only [glyzLineFrequencyBox, mem_setOf_eq, abs_le, mem_Icc]
  constructor
  · intro h
    constructor
    · have := (le_div_iff₀ hδ).mp (show (i : ℝ) + 1 / 2 - 1 ≤ ξ / δ by linarith)
      nlinarith
    · have := (div_le_iff₀ hδ).mp (show ξ / δ ≤ (i : ℝ) + 1 / 2 + 1 by linarith)
      nlinarith
  · intro h
    have hlo : (i : ℝ) + 1 / 2 - 1 ≤ ξ / δ := (le_div_iff₀ hδ).mpr (by nlinarith [h.1])
    have hhi : ξ / δ ≤ (i : ℝ) + 1 / 2 + 1 := (div_le_iff₀ hδ).mpr (by nlinarith [h.2])
    constructor <;> linarith

theorem glyzLineFrequencyBox_overlap (I : Finset ℕ) (δ ξ : ℝ) :
    (I.filter (fun i => ξ ∈ glyzLineFrequencyBox δ i)).card ≤ 3 := by
  let a := ξ / δ - 1 / 2
  let J : Finset ℤ := Finset.Icc (⌊a⌋ - 1) (⌊a⌋ + 1)
  have hm : Set.MapsTo (fun i : ℕ => (i : ℤ))
      (↑(I.filter (fun i => ξ ∈ glyzLineFrequencyBox δ i)) : Set ℕ) (↑J : Set ℤ) := by
    intro i hi
    have hi' : |ξ / δ - ((i : ℝ) + 1 / 2)| ≤ 1 := (Finset.mem_filter.mp hi).2
    have h := abs_le.mp hi'
    have hf := Int.floor_le a
    have hf' := Int.lt_floor_add_one a
    have hlo : ((⌊a⌋ : ℤ) : ℝ) - 1 ≤ (i : ℝ) := by dsimp [a] at *; linarith
    have hhi : (i : ℝ) < ((⌊a⌋ : ℤ) : ℝ) + 2 := by dsimp [a] at *; linarith
    have hlo' : ⌊a⌋ - 1 ≤ (i : ℤ) := by exact_mod_cast hlo
    have hhi' : (i : ℤ) < ⌊a⌋ + 2 := by exact_mod_cast hhi
    change (i : ℤ) ∈ J
    exact Finset.mem_Icc.mpr ⟨hlo', by omega⟩
  have hc := Finset.card_le_card_of_injOn _ hm (fun _ _ _ _ h => Int.ofNat_injective h)
  have hJ : J.card = 3 := by
    dsimp only [J]
    rw [Int.card_Icc, show ⌊a⌋ + 1 + 1 - (⌊a⌋ - 1) = (3 : ℤ) by ring]
    rfl
  exact hJ ▸ hc

/-- Uniform degree-one decoupling, in squared L² mass form. The sets in
the support hypothesis are the actual moment-curve Fourier intervals. -/
theorem glyz_degree_one_lintegral (I : Finset ℕ) (δ : ℝ) (f : ℕ → SchwartzMap ℝ ℂ)
    (hs : ∀ i ∈ I, Function.support (𝓕 (f i : ℝ → ℂ)) ⊆ glyzLineFrequencyBox δ i) :
    (∫⁻ x : ℝ, ‖∑ i ∈ I, f i x‖ₑ ^ (2 : ℕ)) ≤
      3 * ∑ i ∈ I, ∫⁻ x : ℝ, ‖f i x‖ₑ ^ (2 : ℕ) := by
  apply glyz_schwartz_l2_overlap I f 3
  intro ξ
  apply (Finset.card_le_card ?_).trans (glyzLineFrequencyBox_overlap I δ ξ)
  intro i hi
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,
    hs i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2⟩

theorem glyz_degree_one_eLpNorm_sq (I : Finset ℕ) (δ : ℝ) (f : ℕ → SchwartzMap ℝ ℂ)
    (hs : ∀ i ∈ I, Function.support (𝓕 (f i : ℝ → ℂ)) ⊆ glyzLineFrequencyBox δ i) :
    eLpNorm (fun x => ∑ i ∈ I, f i x) 2 volume ^ (2 : ℕ) ≤
      3 * ∑ i ∈ I, eLpNorm (f i) 2 volume ^ (2 : ℕ) := by
  have he (g : ℝ → ℂ) : eLpNorm g 2 volume ^ (2 : ℕ) = ∫⁻ x, ‖g x‖ₑ ^ (2 : ℕ) := by
    simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] using
      (eLpNorm_nnreal_pow_eq_lintegral (f := g) (μ := volume) (p := (2 : ℝ≥0)) (by norm_num))
  simp_rw [he]
  exact glyz_degree_one_lintegral I δ f hs

end PlanarNikodym
