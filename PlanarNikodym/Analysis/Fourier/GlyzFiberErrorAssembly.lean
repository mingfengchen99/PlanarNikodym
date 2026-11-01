import PlanarNikodym.Analysis.Fourier.GlyzFiberPatchTransport

/-! A fixed compact projection controls the integrated fiber error.
The coefficient is selected before the frozen time, scales, and data. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators ContDiff
namespace PlanarNikodym

/-- Actual lower-degree fiber bounds assemble in the original parameter
measure. Only the error incurs the compact unused-coordinate volume. -/
theorem exists_glyz_original_fiber_patch_factor {d m : ℕ}
    (σ : Fin m ↪ Fin (d + 2)) (v : Aux (d + 2))
    (ψ : Cutoff d) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
    ∃ V : ℝ, 0 < V ∧ ∀ (c : ℝ) (F : Parameters 2 d → ℂ), Continuous F →
      ∀ (I : Finset ℕ) (Fj : ℕ → Parameters 2 d → ℂ), (∀ j ∈ I, Continuous (Fj j)) →
      ∀ (p : ℝ), 0 < p → ∀ D e : ℝ≥0∞,
      (∀ u : UnselectedCoordinates σ,
        (∫⁻ z, ‖(ψ (c, glyzFiberParameter σ v u z) : ℂ) *
          F (glyzFiberParameter σ v u z)‖ₑ ^ p) ≤
          D * ∑ j ∈ I, (∫⁻ z, ‖Fj j (glyzFiberParameter σ v u z)‖ₑ ^ p) + e) →
      (∫⁻ x, ‖(ψ (c, x) : ℂ) * F x‖ₑ ^ p) ≤
        D * (∑ j ∈ I, ∫⁻ x, ‖Fj j x‖ₑ ^ p) + ENNReal.ofReal V * e := by
  classical
  let U : Set (UnselectedCoordinates σ) := glyzFiberProjection σ v '' tsupport ψ
  have hU : IsCompact U := hcψ.image (continuous_glyzFiberProjection σ v)
  have hUfin : volume U ≠ ⊤ := hU.measure_lt_top.ne
  let V : ℝ := (volume U).toReal + 1
  have hV : 0 < V := by dsimp only [V]; positivity
  have hUV : volume U ≤ ENNReal.ofReal V := by
    rw [← ENNReal.ofReal_toReal hUfin]
    exact ENNReal.ofReal_le_ofReal (by dsimp only [V]; linarith)
  refine ⟨V, hV, fun c F hF I Fj hFj p hp D e hstep => ?_⟩
  let A := fun u : UnselectedCoordinates σ => ∫⁻ z : Aux m,
    ‖(ψ (c, glyzFiberParameter σ v u z) : ℂ) * F (glyzFiberParameter σ v u z)‖ₑ ^ p
  let B := fun u : UnselectedCoordinates σ =>
    ∑ j ∈ I, ∫⁻ z : Aux m, ‖Fj j (glyzFiberParameter σ v u z)‖ₑ ^ p
  have hAj : Function.support A ⊆ U := by
    intro u hu
    by_contra hnot
    have hz (z : Aux m) : ψ (c, glyzFiberParameter σ v u z) = 0 := by
      by_contra hne
      apply hnot
      exact ⟨(c, glyzFiberParameter σ v u z), subset_tsupport _ hne,
        glyzFiberProjection_fiber σ v c u z⟩
    apply hu
    simp only [A, hz, Complex.ofReal_zero, zero_mul, enorm_zero,
      ENNReal.zero_rpow_of_pos hp, lintegral_zero]
  have hmj (j : ℕ) (hj : j ∈ I) : Measurable (fun u : UnselectedCoordinates σ =>
      ∫⁻ z : Aux m, ‖Fj j (glyzFiberParameter σ v u z)‖ₑ ^ p) := by
    have hm : Measurable (fun uz : UnselectedCoordinates σ × Aux m =>
        ‖Fj j (glyzFiberParameter σ v uz.1 uz.2)‖ₑ ^ p) :=
      ((hFj j hj).comp (continuous_glyzFiberParameter σ v)).measurable.enorm.pow_const p
    exact hm.lintegral_prod_right
  have hmB : Measurable B := Finset.measurable_sum I hmj
  have hBint : (∫⁻ u : UnselectedCoordinates σ, B u) = ∑ j ∈ I, ∫⁻ x, ‖Fj j x‖ₑ ^ p := by
    rw [show (∫⁻ u : UnselectedCoordinates σ, B u) =
      ∑ j ∈ I, ∫⁻ u : UnselectedCoordinates σ, ∫⁻ z : Aux m,
        ‖Fj j (glyzFiberParameter σ v u z)‖ₑ ^ p from lintegral_finsetSum I hmj]
    apply Finset.sum_congr rfl
    intro j hj
    exact (glyz_lintegral_original_fibers σ v _ ((hFj j hj).measurable.enorm.pow_const p)).symm
  have hmF : Measurable (fun x => ‖(ψ (c, x) : ℂ) * F x‖ₑ ^ p) :=
    ((Complex.continuous_ofReal.comp (hψ.comp (continuous_const.prodMk continuous_id))).mul hF).measurable.enorm.pow_const p
  calc
    _ = ∫⁻ u : UnselectedCoordinates σ, A u := glyz_lintegral_original_fibers σ v _ hmF
    _ = ∫⁻ u in U, A u := (setLIntegral_eq_of_support_subset hAj).symm
    _ ≤ ∫⁻ u in U, D * B u + e := lintegral_mono hstep
    _ = D * (∫⁻ u in U, B u) + e * volume U := by
      rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hmB, setLIntegral_const]
    _ ≤ D * (∫⁻ u : UnselectedCoordinates σ, B u) + e * ENNReal.ofReal V := by
      exact add_le_add (mul_le_mul_right (lintegral_mono' Measure.restrict_le_self le_rfl) D)
        (mul_le_mul_right hUV e)
    _ = _ := by rw [hBint, mul_comm e]

end PlanarNikodym
