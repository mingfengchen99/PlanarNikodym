import PlanarNikodym.Analysis.Fourier.E3SmoothUniformLinearL2
import PlanarNikodym.Analysis.Fourier.TimeRestrictedL2Partition

/-! Uniform square sums of the actual original time slices for C∞
phases. The geometric data contain smooth charts and exact identities,
and every operator and amplitude estimate is proved. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace PlanarNikodym

def E3TimeSliceChartGeometry {d : ℕ} (G : Family 2 d)
    (E : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux 2)
      ((ℝ × Aux (d + 2)) × Aux 2))
    (σ : Fin 2 ↪ Fin (d + 2)) (T : Set ((ℝ × Aux (d + 2)) × Aux 2))
    (b δ : ℝ) (N : ℕ) (β : ℝ) (v : ℕ → Aux (d + 2))
    (e : ℕ → OpenPartialHomeomorph (Aux 2) (Aux 2)) (K : ℕ → Set (Aux 2))
    (hm : 2 ≤ d + 2) : Prop :=
  ∀ i ∈ Finset.range N,
    (∀ z, e i z = G.lowerCinematicJetMap hm σ (b + (i : ℝ) * δ) (v i) z) ∧
    (∀ x ∈ (e i).source, ContDiffAt ℝ ∞ (e i) x) ∧
    MeasurableSet (K i) ∧ K i ⊆ (e i).source ∧
    (∀ z ∈ K i, β ≤ |LinearMap.det (fderiv ℝ (e i) z).toLinearMap|) ∧
    (∀ y ∈ e i '' K i, ((b + (i : ℝ) * δ, v i), y) ∈ T) ∧
    (∀ y ∈ e i '' K i, (E.symm ((b + (i : ℝ) * δ, v i), y)).2 = (e i).symm y)

theorem Family.exists_e3_uniform_local_timeSlice_square_sum_bound
    {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (E : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux 2)
      ((ℝ × Aux (d + 2)) × Aux 2))
    (hi : ∀ x ∈ E.target, ContDiffAt ℝ ∞ E.symm x) (σ : Fin 2 ↪ Fin (d + 2))
    (a : Parameters 2 d × ℝ × ℝ → ℂ) (ha : ContDiff ℝ ∞ a)
    {T : Set ((ℝ × Aux (d + 2)) × Aux 2)} (hT : IsCompact T) (hTE : T ⊆ E.target)
    {J : Set ℝ} (hJ : IsCompact J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b δ : ℝ) (N : ℕ) (v : ℕ → Aux (d + 2))
      (e : ℕ → OpenPartialHomeomorph (Aux 2) (Aux 2)) (K : ℕ → Set (Aux 2))
      (hm : 2 ≤ d + 2) (β : ℝ), 0 ≤ β →
      E3TimeSliceChartGeometry G E σ T b δ N β v e K hm →
      ∀ h : Plane → ℂ, StronglyMeasurable h → MemLp h 2 volume →
      ∀ κ r : ℝ, 0 < κ → 0 < r → 0 < δ → δ ≤ 1 →
      (2 * Real.pi * r) * δ ^ (2 : ℕ) ∈ Icc (0 : ℝ) 1 →
      (∀ x : Plane, |x.2| < κ → h x = 0) →
      (∀ x : Plane, x.2 ∉ J → h x = 0) →
      ENNReal.ofReal β * (∑ i ∈ Finset.range N, ∫⁻ z in K i,
        ‖timeSliceExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) a h
          (2 * Real.pi * r) (b + (i : ℝ) * δ) δ
          (parameterFrame d (v i + coordinateInsertion σ z))‖ₑ ^ (2 : ℕ)) ≤
        (3 : ℝ≥0∞) * ENNReal.ofReal (C ^ (2 : ℕ) * κ⁻¹ * r⁻¹ ^ (2 : ℕ)) *
          ∫⁻ x : Plane, ‖h x‖ₑ ^ (2 : ℕ) := by
  obtain ⟨C, hC, hsingle⟩ := G.exists_e3_uniform_linear_chart_slice_sq_bound
    hG E hi σ a ha hT hTE hJ
  refine ⟨C, hC, ?_⟩
  intro b δ N v e K hm β hβ hgeom h hh h2 κ r hκ hr hδ hδ1 hα hgap hvertical
  let A := ENNReal.ofReal (C ^ (2 : ℕ) * κ⁻¹ * r⁻¹ ^ (2 : ℕ))
  have hpiece (i : ℕ) (hiN : i ∈ Finset.range N) :
      ENNReal.ofReal β * (∫⁻ z in K i,
        ‖timeSliceExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) a h
          (2 * Real.pi * r) (b + (i : ℝ) * δ) δ
          (parameterFrame d (v i + coordinateInsertion σ z))‖ₑ ^ (2 : ℕ)) ≤
        A * ∫⁻ x : Plane, ‖timeRestrictedData b δ i h x‖ₑ ^ (2 : ℕ) := by
    obtain ⟨he, hea, hK, hKS, hJac, himage, hinverse⟩ := hgeom i hiN
    have hhᵢ := stronglyMeasurable_timeRestrictedData b δ i hh
    have h1ᵢ := integrable_timeRestrictedData_of_vertical b hδ i h2 hJ hvertical
    have h2ᵢ := memLp_timeRestrictedData_two b δ i h2
    have hverticalᵢ : ∀ x : Plane, x.2 ∉ J → timeRestrictedData b δ i h x = 0 := by
      intro x hx
      simp [timeRestrictedData, hvertical x hx]
    have hs := hsingle (b + (i : ℝ) * δ) (v i) (e i) hm he hea
      (K i) hK hKS β hβ hJac himage hinverse (timeRestrictedData b δ i h)
      hhᵢ.measurable h1ᵢ h2ᵢ κ r δ hκ hr hδ hδ1 hα
      (timeRestrictedData_eq_zero_of_gap hgap b δ i) hverticalᵢ
    simpa only [timeSliceExtension_timeRestrictedData _ _ h (2 * Real.pi * r) b hδ i] using hs
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ i ∈ Finset.range N, A * ∫⁻ x : Plane,
        ‖timeRestrictedData b δ i h x‖ₑ ^ (2 : ℕ) := Finset.sum_le_sum hpiece
    _ = A * ∑ i ∈ Finset.range N, ∫⁻ x : Plane,
        ‖timeRestrictedData b δ i h x‖ₑ ^ (2 : ℕ) := (Finset.mul_sum ..).symm
    _ ≤ A * ((3 : ℝ≥0∞) * ∫⁻ x : Plane, ‖h x‖ₑ ^ (2 : ℕ)) :=
      mul_le_mul_right (sum_lintegral_timeRestrictedData_sq_le b hδ N hh) A
    _ = _ := by dsimp only [A]; ac_rfl

/-- The original input is only L¹∩L². Its true compact-symbol partial
inverse data supply the vertical support, gap and `r⁻³` squared mass. -/
theorem Family.exists_e3_uniform_weighted_timeSlice_square_sum_bound
    {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (E : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux 2)
      ((ℝ × Aux (d + 2)) × Aux 2))
    (hi : ∀ x ∈ E.target, ContDiffAt ℝ ∞ E.symm x) (σ : Fin 2 ↪ Fin (d + 2))
    (a : Parameters 2 d × ℝ × ℝ → ℂ) (ha : ContDiff ℝ ∞ a)
    {T : Set ((ℝ × Aux (d + 2)) × Aux 2)} (hT : IsCompact T) (hTE : T ⊆ E.target)
    {m : Plane → ℝ} (hm : Continuous m) (hmc : HasCompactSupport m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b δ : ℝ) (N : ℕ) (v : ℕ → Aux (d + 2))
      (e : ℕ → OpenPartialHomeomorph (Aux 2) (Aux 2)) (K : ℕ → Set (Aux 2))
      (hd : 2 ≤ d + 2) (β M : ℝ), 0 ≤ β →
      E3TimeSliceChartGeometry G E σ T b δ N β v e K hd →
      (∀ ξ : Plane, |m ξ| ≤ M) →
      ∀ f : Plane → ℂ, Integrable f → MemLp f 2 volume →
      ∀ κ r : ℝ, 0 < κ → 0 < r → 0 < δ → δ ≤ 1 →
      (2 * Real.pi * r) * δ ^ (2 : ℕ) ∈ Icc (0 : ℝ) 1 →
      (∀ ξ : Plane, |ξ.2| < κ → m ξ = 0) →
      ENNReal.ofReal β * (∑ i ∈ Finset.range N, ∫⁻ z in K i,
        ‖timeSliceExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) a
          (fun x => weightedPartialFourierData m f r x.1 x.2)
          (2 * Real.pi * r) (b + (i : ℝ) * δ) δ
          (parameterFrame d (v i + coordinateInsertion σ z))‖ₑ ^ (2 : ℕ)) ≤
        (3 : ℝ≥0∞) * ENNReal.ofReal (C ^ (2 : ℕ) * κ⁻¹ * r⁻¹ ^ (2 : ℕ)) *
          (ENNReal.ofReal (M ^ (2 : ℕ) * r⁻¹ ^ (3 : ℕ)) *
            ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ)) := by
  obtain ⟨C, hC, hsum⟩ := G.exists_e3_uniform_local_timeSlice_square_sum_bound
    hG E hi σ a ha hT hTE (hmc.isCompact.image continuous_snd)
  refine ⟨C, hC, ?_⟩
  intro b δ N v e K hd β M hβ hgeom hM f h1 h2 κ r hκ hr hδ hδ1 hα hgap
  have hh := stronglyMeasurable_partialFourierData (weighted_scaledFourierData_continuous hm h1 r) r
  have hd2 := memLp_weightedPartialFourierData_two hm hmc h1 hr
  have hs := hsum b δ N v e K hd β hβ hgeom
    (fun x => weightedPartialFourierData m f r x.1 x.2) hh hd2 κ r hκ hr hδ hδ1 hα
    (fun x hx => weightedPartialFourierData_eq_zero_of_gap hgap r x.1 x.2 hx)
    (fun x hx => weightedPartialFourierData_eq_zero_of_vertical r x.1 x.2 hx)
  exact hs.trans (mul_le_mul_right
    (lintegral_weightedPartialFourierData_sq_le_of_integrable hm hmc h1 h2 hr hM) _)


end PlanarNikodym
