import PlanarNikodym.Analysis.Maximal.E2FIOTwoDimNonstationary
import PlanarNikodym.Analysis.Maximal.E2FIOAmplitudePartition

/-! Coordinate changes and smooth coordinate selection for the actual
uniform two-dimensional nonstationary phase estimate. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology Manifold
namespace PlanarNikodym
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def e2FIOFirstCoordinateDerivative (Φ : P × Plane → ℝ) (z : P × Plane) : ℝ :=
  deriv (fun s : ℝ => Φ (z.1, (s, z.2.2))) z.2.1

theorem e2FIOSecondCoordinateDerivative_contDiff {Φ : P × Plane → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (e2FIOSecondCoordinateDerivative Φ) := by
  have hh : ContDiff ℝ ∞ (fun z : (P × ℝ) × ℝ => Φ (z.1.1, (z.1.2, z.2))) :=
    hΦ.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))
  exact (contDiff_partialTimeDeriv hh).comp
    ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd)

theorem e2FIOFirstCoordinateDerivative_contDiff {Φ : P × Plane → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (e2FIOFirstCoordinateDerivative Φ) := by
  have hh : ContDiff ℝ ∞ (fun z : (P × ℝ) × ℝ => Φ (z.1.1, (z.2, z.1.2))) :=
    hΦ.comp (contDiff_fst.fst.prodMk (contDiff_snd.prodMk contDiff_fst.snd))
  exact (contDiff_partialTimeDeriv hh).comp
    ((contDiff_fst.prodMk contDiff_snd.snd).prodMk contDiff_snd.fst)

theorem e2_exists_uniform_first_coordinate_nonstationary_decay
    {Φ : P × Plane → ℝ} {a : P × Plane → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hne : ∀ z ∈ tsupport a, e2FIOFirstCoordinateDerivative Φ z ≠ 0) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : P) (r : ℝ), r ≠ 0 →
      ‖∫ q : Plane, Complex.exp (((r * Φ (p, q) : ℝ) : ℂ) * Complex.I) * a (p, q)‖ ≤
        C * (|r|⁻¹) ^ N := by
  let e : (P × Plane) ≃ₜ (P × Plane) :=
    (Homeomorph.refl P).prodCongr (Homeomorph.prodComm ℝ ℝ)
  have he (z : P × Plane) : e z = (z.1, (z.2.2, z.2.1)) := rfl
  let Ψ := Φ ∘ e
  let b := a ∘ e
  have hΨ : ContDiff ℝ ∞ Ψ :=
    hΦ.comp (contDiff_fst.prodMk (contDiff_snd.snd.prodMk contDiff_snd.fst))
  have hb : ContDiff ℝ ∞ b :=
    ha.comp (contDiff_fst.prodMk (contDiff_snd.snd.prodMk contDiff_snd.fst))
  have hbc : HasCompactSupport b := hc.comp_homeomorph e
  have hne' : ∀ z ∈ tsupport b, e2FIOSecondCoordinateDerivative Ψ z ≠ 0 := by
    intro z hz
    exact hne (e z) (tsupport_comp_subset_preimage a e.continuous hz)
  obtain ⟨C, hC, h⟩ := e2_exists_uniform_second_coordinate_nonstationary_decay hΨ hb hbc hne' N
  refine ⟨C, hC, ?_⟩
  intro p r hr
  have hh := h p r hr
  have heq : (∫ q : Plane, Complex.exp (((r * Ψ (p, q) : ℝ) : ℂ) * Complex.I) * b (p, q)) =
      ∫ q : Plane, Complex.exp (((r * Φ (p, q) : ℝ) : ℂ) * Complex.I) * a (p, q) := by
    simp only [Ψ, b, Function.comp_apply, he]
    rw [Measure.volume_eq_prod]
    exact integral_prod_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (fun q : Plane => Complex.exp (((r * Φ (p, q) : ℝ) : ℂ) * Complex.I) * a (p, q))
  rwa [heq] at hh


omit [NormedSpace ℝ P] in
theorem e2_fio_slice_integrable {Φ : P × Plane → ℝ} {a : P × Plane → ℂ}
    (hΦ : Continuous Φ) (ha : Continuous a) (hc : HasCompactSupport a)
    (p : P) (r : ℝ) :
    Integrable (fun q : Plane => Complex.exp (((r * Φ (p, q) : ℝ) : ℂ) * Complex.I) * a (p, q)) := by
  have hJ : Continuous (fun q : Plane =>
      Complex.exp (((r * Φ (p, q) : ℝ) : ℂ) * Complex.I) * a (p, q)) :=
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (continuous_const.mul (hΦ.comp (continuous_const.prodMk continuous_id)))).mul
        continuous_const)).mul (ha.comp (continuous_const.prodMk continuous_id))
  apply hJ.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (hc.isCompact.image continuous_snd)
  intro q hq
  have hz : a (p, q) = 0 := by
    by_contra hn
    exact hq ⟨(p, q), subset_tsupport a hn, rfl⟩
  rw [hz, mul_zero]

variable [FiniteDimensional ℝ P]

theorem e2_exists_uniform_two_dimensional_nonstationary_decay
    {Φ : P × Plane → ℝ} {a : P × Plane → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hne : ∀ z ∈ tsupport a, e2FIOFirstCoordinateDerivative Φ z ≠ 0 ∨
      e2FIOSecondCoordinateDerivative Φ z ≠ 0) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : P) (r : ℝ), r ≠ 0 →
      ‖∫ q : Plane, Complex.exp (((r * Φ (p, q) : ℝ) : ℂ) * Complex.I) * a (p, q)‖ ≤
        C * (|r|⁻¹) ^ N := by
  classical
  let U : Fin 2 → Set (P × Plane) := fun j =>
    if j = 0 then {z | e2FIOFirstCoordinateDerivative Φ z ≠ 0}
    else {z | e2FIOSecondCoordinateDerivative Φ z ≠ 0}
  have hU (j : Fin 2) : IsOpen (U j) := by
    fin_cases j
    · exact isOpen_ne_fun (e2FIOFirstCoordinateDerivative_contDiff hΦ).continuous continuous_const
    · exact isOpen_ne_fun (e2FIOSecondCoordinateDerivative_contDiff hΦ).continuous continuous_const
  have hcover : tsupport a ⊆ ⋃ j : Fin 2, U j := by
    intro z hz
    rcases hne z hz with hh | hh
    · exact mem_iUnion.mpr ⟨0, by simpa [U] using hh⟩
    · exact mem_iUnion.mpr ⟨1, by simpa [U] using hh⟩
  obtain ⟨b, hbAll, hsum⟩ := e2_exists_complex_amplitude_partition ha hc U hU hcover
  have hb (j : Fin 2) : ContDiff ℝ ∞ (b j) := (hbAll j).1
  have hbc (j : Fin 2) : HasCompactSupport (b j) := (hbAll j).2.1
  have hbs (j : Fin 2) : tsupport (b j) ⊆ U j := (hbAll j).2.2
  have hex (j : Fin 2) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : P) (r : ℝ), r ≠ 0 →
      ‖∫ q : Plane, Complex.exp (((r * Φ (p, q) : ℝ) : ℂ) * Complex.I) * b j (p, q)‖ ≤
        C * (|r|⁻¹) ^ N := by
    fin_cases j
    · exact e2_exists_uniform_first_coordinate_nonstationary_decay hΦ (hb 0) (hbc 0)
        (fun z hz => by simpa [U] using hbs 0 hz) N
    · exact e2_exists_uniform_second_coordinate_nonstationary_decay hΦ (hb 1) (hbc 1)
        (fun z hz => by simpa [U] using hbs 1 hz) N
  choose C hC hdecay using hex
  refine ⟨∑ j : Fin 2, C j, Finset.sum_nonneg (fun j _ => hC j), ?_⟩
  intro p r hr
  have hint (j : Fin 2) : Integrable (fun q : Plane =>
      Complex.exp (((r * Φ (p, q) : ℝ) : ℂ) * Complex.I) * b j (p, q)) :=
    e2_fio_slice_integrable hΦ.continuous (hb j).continuous (hbc j) p r
  have heq : (fun q : Plane => Complex.exp (((r * Φ (p, q) : ℝ) : ℂ) * Complex.I) * a (p, q)) =
      fun q : Plane => ∑ j : Fin 2,
        Complex.exp (((r * Φ (p, q) : ℝ) : ℂ) * Complex.I) * b j (p, q) := by
    funext q
    rw [← Finset.mul_sum, hsum]
  rw [heq, integral_finsetSum _ (fun j _ => hint j)]
  calc
    _ ≤ ∑ j : Fin 2, ‖∫ q : Plane,
        Complex.exp (((r * Φ (p, q) : ℝ) : ℂ) * Complex.I) * b j (p, q)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 2, C j * (|r|⁻¹) ^ N := Finset.sum_le_sum (fun j _ => hdecay j p r hr)
    _ = _ := (Finset.sum_mul _ _ _).symm

end PlanarNikodym
