import PlanarNikodym.Analysis.Fourier.PartialExtensionLocalization

/-! The exact squared L² prefactor of the original microlocal main
pieces, retaining the real compact symbol and the original input. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

theorem Family.lintegral_cutoffPartialExtension_scaleTimeLocalized_sq
    {d : ℕ} (G : Family 2 d) (χ : Cutoff d) (L : FrequencyCutoff) (β : ℝ → ℝ)
    (r b : ℝ) {δ : ℝ} (hδ : δ ≠ 0) (i : ℕ) (f : Plane → ℂ)
    (σ : Fin 2 ↪ Fin (d + 2)) (v : Aux (d + 2)) (K : Set (Aux 2)) :
    (∫⁻ z in K, ‖G.cutoffPartialExtension (scaleTimeLocalizedCutoff χ b δ i) L β r f
      (parameterFrame d (v + coordinateInsertion σ z))‖ₑ ^ (2 : ℕ)) =
      ENNReal.ofReal (r ^ (4 : ℕ)) * ∫⁻ z in K,
        ‖timeSliceExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1)
          (fun x => (χ (x.2.1, x.1) : ℂ))
          (fun x => weightedPartialFourierData (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2)
            f r x.1 x.2) (2 * Real.pi * r) (b + (i : ℝ) * δ) δ
          (parameterFrame d (v + coordinateInsertion σ z))‖ₑ ^ (2 : ℕ) := by
  simp_rw [G.cutoffPartialExtension_scaleTimeLocalized χ L β r b hδ i f,
    enorm_smul, Real.enorm_eq_ofReal (sq_nonneg r), mul_pow,
    ← ENNReal.ofReal_pow (sq_nonneg r), ← pow_mul,
    show (2 : ℕ) * 2 = 4 from rfl]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem Family.sum_lintegral_cutoffPartialExtension_scaleTimeLocalized_sq
    {d : ℕ} (G : Family 2 d) (χ : Cutoff d) (L : FrequencyCutoff) (β : ℝ → ℝ)
    (r b : ℝ) {δ : ℝ} (hδ : δ ≠ 0) (N : ℕ) (f : Plane → ℂ)
    (σ : Fin 2 ↪ Fin (d + 2)) (v : ℕ → Aux (d + 2)) (K : ℕ → Set (Aux 2)) :
    (∑ i ∈ Finset.range N, ∫⁻ z in K i,
      ‖G.cutoffPartialExtension (scaleTimeLocalizedCutoff χ b δ i) L β r f
        (parameterFrame d (v i + coordinateInsertion σ z))‖ₑ ^ (2 : ℕ)) =
      ENNReal.ofReal (r ^ (4 : ℕ)) * ∑ i ∈ Finset.range N, ∫⁻ z in K i,
        ‖timeSliceExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1)
          (fun x => (χ (x.2.1, x.1) : ℂ))
          (fun x => weightedPartialFourierData (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2)
            f r x.1 x.2) (2 * Real.pi * r) (b + (i : ℝ) * δ) δ
          (parameterFrame d (v i + coordinateInsertion σ z))‖ₑ ^ (2 : ℕ) := by
  simp_rw [G.lintegral_cutoffPartialExtension_scaleTimeLocalized_sq χ L β r b hδ]
  exact (Finset.mul_sum _ _ _).symm

end PlanarNikodym
