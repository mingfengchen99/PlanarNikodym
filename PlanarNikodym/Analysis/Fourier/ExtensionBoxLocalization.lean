import PlanarNikodym.Analysis.Fourier.TimeSliceExtension
import PlanarNikodym.Analysis.Localization.CoefficientBoxPartition
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! The expanding coefficient domain is reduced to actual unit-box
extension operators, using the constructed smooth partition. -/
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal
namespace PlanarNikodym

theorem polynomialExtension_mul_coefficient {n : ℕ}
    (b : Aux (n + 1) → ℝ → ℝ → ℂ) (h : ℝ × ℝ → ℂ)
    (R : ℝ) (φ : Aux (n + 1) → ℂ) (w : Aux (n + 1)) :
    polynomialExtension (fun w τ η => φ w * b w τ η) h R w = φ w * polynomialExtension b h R w := by
  unfold polynomialExtension
  simp_rw [show ∀ η τ, phaseOscillation (jetPolynomial w) (R * η) τ * (φ w * b w τ η) * h (τ, η) =
    φ w * (phaseOscillation (jetPolynomial w) (R * η) τ * b w τ η * h (τ, η)) by intros; ring]
  simp_rw [integral_const_mul]

theorem stronglyMeasurable_polynomialExtension {n : ℕ}
    {b : Aux (n + 1) → ℝ → ℝ → ℂ}
    (hb : StronglyMeasurable (fun x : (Aux (n + 1) × ℝ) × ℝ => b x.1.1 x.2 x.1.2))
    {h : ℝ × ℝ → ℂ} (hh : StronglyMeasurable h) (R : ℝ) :
    StronglyMeasurable (polynomialExtension b h R) := by
  have hp : Continuous (fun x : (Aux (n + 1) × ℝ) × ℝ =>
      phaseOscillation (jetPolynomial x.1.1) (R * x.1.2) x.2) := by
    unfold phaseOscillation jetPolynomial
    fun_prop
  have hi := (hp.stronglyMeasurable.mul hb).mul (hh.comp_measurable
    (measurable_snd.prodMk measurable_fst.snd))
  exact hi.integral_prod_right'.integral_prod_right'

theorem exists_unitBox_polynomialExtension_partition {n : ℕ}
    {K : Set (Aux (n + 1))} (hK : IsCompact K)
    (b : Aux (n + 1) → ℝ → ℝ → ℂ) (h : ℝ × ℝ → ℂ) (R : ℝ) :
    ∃ a : ℝ, ∃ N : ℕ, ∀ w ∈ K,
      polynomialExtension b h R w =
        ∑ k ∈ Fintype.piFinset (fun _ : Fin (n + 1) => Finset.range N),
          polynomialExtension (fun w τ η => (coefficientBoxCutoff a k w : ℂ) * b w τ η) h R w := by
  obtain ⟨a, N, hpart⟩ := exists_coefficientBoxCutoff_partition hK
  refine ⟨a, N, ?_⟩
  intro w hw
  simp_rw [polynomialExtension_mul_coefficient]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, hpart w hw, Complex.ofReal_one, one_mul]

set_option maxHeartbeats 600000 in
theorem polynomialExtension_boxPartition_eLpNorm_le {n : ℕ}
    {K : Set (Aux (n + 1))} (hK : IsCompact K)
    {b : Aux (n + 1) → ℝ → ℝ → ℂ}
    (hb : StronglyMeasurable (fun x : (Aux (n + 1) × ℝ) × ℝ => b x.1.1 x.2 x.1.2))
    {h : ℝ × ℝ → ℂ} (hh : StronglyMeasurable h) (R : ℝ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    ∃ a : ℝ, ∃ N : ℕ,
      eLpNorm (polynomialExtension b h R) p (volume.restrict K) ≤
        ∑ k ∈ Fintype.piFinset (fun _ : Fin (n + 1) => Finset.range N),
          eLpNorm (polynomialExtension
            (fun w τ η => (coefficientBoxCutoff a k w : ℂ) * b w τ η) h R) p (volume.restrict K) := by
  obtain ⟨a, N, hpart⟩ := exists_unitBox_polynomialExtension_partition hK b h R
  refine ⟨a, N, ?_⟩
  let I := Fintype.piFinset (fun _ : Fin (n + 1) => Finset.range N)
  let T := fun k : Fin (n + 1) → ℕ => polynomialExtension
    (fun w τ η => (coefficientBoxCutoff a k w : ℂ) * b w τ η) h R
  have he : polynomialExtension b h R =ᵐ[volume.restrict K] ∑ k ∈ I, T k := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with w hw
    simpa only [Finset.sum_apply] using hpart w hw
  rw [eLpNorm_congr_ae he]
  apply eLpNorm_sum_le (f := T) (s := I) _ hp
  intro k _
  have hφ : StronglyMeasurable (fun x : (Aux (n + 1) × ℝ) × ℝ =>
      (coefficientBoxCutoff a k x.1.1 : ℂ)) :=
    (Complex.continuous_ofReal.comp ((contDiff_coefficientBoxCutoff a k).continuous.comp
      continuous_fst.fst)).stronglyMeasurable
  exact (stronglyMeasurable_polynomialExtension (hφ.mul hb) hh R).aestronglyMeasurable

end PlanarNikodym
