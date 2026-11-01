import PlanarNikodym.Analysis.Fourier.CompactKernelIntegration

/-! A genuine locally cut off variable-coefficient extension, its
Schwartz realization for L¹ data, and the exact spatial freezing identity. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform
namespace PlanarNikodym

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def localizedVariableKernel (χ : E → ℂ) (a : E × Plane → ℂ)
    (Φ : E × ℝ → ℝ) (L : ℝ) (w : E) (δ : ℝ) (q : E × Plane) : ℂ :=
  χ q.1 * Complex.exp (((L * q.2.2 * Φ (w + δ • q.1, q.2.1) : ℝ) : ℂ) * Complex.I) *
    a (w + δ • q.1, q.2)

omit [FiniteDimensional ℝ E] in
theorem contDiff_localizedVariableKernel {χ : E → ℂ}
    (hχ : ContDiff ℝ ∞ χ) {a : E × Plane → ℂ} (ha : ContDiff ℝ ∞ a)
    {Φ : E × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (L : ℝ) (w : E) (δ : ℝ) :
    ContDiff ℝ ∞ (localizedVariableKernel χ a Φ L w δ) := by
  have hr : ContDiff ℝ ∞ (fun q : E × Plane =>
      L * q.2.2 * Φ (w + δ • q.1, q.2.1)) :=
    (contDiff_const.mul contDiff_snd.snd).mul (hΦ.comp (by fun_prop))
  have hp : ContDiff ℝ ∞ (fun q : E × Plane =>
      ((L * q.2.2 * Φ (w + δ • q.1, q.2.1) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hr
  exact ((hχ.comp contDiff_fst).mul
    (Complex.contDiff_exp.comp (hp.mul contDiff_const))).mul (ha.comp (by fun_prop))

omit [FiniteDimensional ℝ E] in
theorem hasCompactSupport_localizedVariableKernel {χ : E → ℂ}
    (hcχ : HasCompactSupport χ) {a : E × Plane → ℂ} (hca : HasCompactSupport a)
    (Φ : E × ℝ → ℝ) (L : ℝ) (w : E) (δ : ℝ) :
    HasCompactSupport (localizedVariableKernel χ a Φ L w δ) := by
  apply HasCompactSupport.intro (hcχ.isCompact.prod (hca.isCompact.image continuous_snd))
  intro q hq
  by_cases hx : q.1 ∈ tsupport χ
  · have hy : q.2 ∉ Prod.snd '' tsupport a := fun h => hq ⟨hx, h⟩
    have ha : a (w + δ • q.1, q.2) = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hy ⟨(w + δ • q.1, q.2), h, rfl⟩
    simp [localizedVariableKernel, ha]
  · simp [localizedVariableKernel, image_eq_zero_of_notMem_tsupport hx]

def localizedVariableExtension (χ : E → ℂ) (a : E × Plane → ℂ)
    (Φ : E × ℝ → ℝ) (L : ℝ) (w : E) (δ : ℝ) (g : Plane → ℂ) (z : E) : ℂ :=
  ∫ y, g y * localizedVariableKernel χ a Φ L w δ (z, y)

def localizedVariableExtensionSchwartz
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (a : E × Plane → ℂ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (Φ : E × ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (L : ℝ) (w : E) (δ : ℝ) (g : Plane → ℂ) (hg : Integrable g) :
    SchwartzMap E ℂ :=
  compactKernelIntegralSchwartz volume g hg (localizedVariableKernel χ a Φ L w δ)
    (contDiff_localizedVariableKernel hχ ha hΦ L w δ)
    (hasCompactSupport_localizedVariableKernel hcχ hca Φ L w δ)

omit [FiniteDimensional ℝ E] in
@[simp] theorem localizedVariableExtensionSchwartz_apply
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (a : E × Plane → ℂ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (Φ : E × ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (L : ℝ) (w : E) (δ : ℝ) (g : Plane → ℂ) (hg : Integrable g) (z : E) :
    localizedVariableExtensionSchwartz χ hχ hcχ a ha hca Φ hΦ L w δ g hg z =
      localizedVariableExtension χ a Φ L w δ g z := rfl

/-- The local error amplitude carries the actual quadratic Taylor
correction; all parameters remain explicit. -/
def localizedFrozenAmplitude (χ : E → ℂ) (a : E × Plane → ℂ)
    (Φ : E × ℝ → ℝ) (q : E × (E × Plane) × ℝ × ℝ) : ℂ :=
  χ q.1 * frozenSpatialAmplitude a Φ (q.2.1.2, ((q.2.1.1, q.1), q.2.2))

theorem contDiff_localizedFrozenAmplitude {χ : E → ℂ}
    (hχ : ContDiff ℝ ∞ χ) {a : E × Plane → ℂ} (ha : ContDiff ℝ ∞ a)
    {Φ : E × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (localizedFrozenAmplitude χ a Φ) := by
  exact (hχ.comp contDiff_fst).mul
    ((contDiff_frozenSpatialAmplitude ha hΦ).comp (by fun_prop))

omit [FiniteDimensional ℝ E] in
theorem tsupport_localizedFrozenAmplitude_fiber_subset (χ : E → ℂ)
    (a : E × Plane → ℂ) (Φ : E × ℝ → ℝ) (q : (E × Plane) × ℝ × ℝ) :
    tsupport (fun z => localizedFrozenAmplitude χ a Φ (z, q)) ⊆ tsupport χ :=
  tsupport_mul_subset_left

def localizedFrozenAmplitudeSchwartz
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (a : E × Plane → ℂ) (ha : ContDiff ℝ ∞ a)
    (Φ : E × ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (q : (E × Plane) × ℝ × ℝ) :
    SchwartzMap E ℂ :=
  (hcχ.mul_right (f' := fun z =>
    frozenSpatialAmplitude a Φ (q.1.2, ((q.1.1, z), q.2)))).toSchwartzMap
      ((contDiff_localizedFrozenAmplitude hχ ha hΦ).comp
        (contDiff_id.prodMk contDiff_const))

@[simp] theorem localizedFrozenAmplitudeSchwartz_apply
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (a : E × Plane → ℂ) (ha : ContDiff ℝ ∞ a)
    (Φ : E × ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (q : (E × Plane) × ℝ × ℝ) (z : E) :
    localizedFrozenAmplitudeSchwartz χ hχ hcχ a ha Φ hΦ q z =
      localizedFrozenAmplitude χ a Φ (z, q) := rfl

omit [FiniteDimensional ℝ E] in
theorem localizedVariableKernel_eq_frozen {Φ : E × ℝ → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (χ : E → ℂ) (a : E × Plane → ℂ)
    (L δ : ℝ) (w z : E) (y : Plane) :
    localizedVariableKernel χ a Φ L w δ (z, y) =
      Complex.exp (((L * y.2 * Φ (w, y.1) : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((L * δ * y.2 * frozenSpatialPhase Φ w z y.1 : ℝ) : ℂ) * Complex.I) *
      localizedFrozenAmplitude χ a Φ (z, ((w, y), (L * δ ^ 2, δ))) := by
  rw [localizedVariableKernel, exp_spatialPhase_eq_frozen_mul_correction hΦ]
  unfold localizedFrozenAmplitude frozenSpatialAmplitude
  ring

theorem localizedFrozenAmplitude_uniform_jets
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (a : E × Plane → ℂ) (ha : ContDiff ℝ ∞ a)
    (Φ : E × ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    {K : Set (E × Plane)} (hK : IsCompact K) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : (E × Plane) × ℝ × ℝ,
      q.1 ∈ K → q.2.1 ∈ Icc (0 : ℝ) 1 → q.2.2 ∈ Icc (0 : ℝ) 1 → ∀ z,
      ‖iteratedFDeriv ℝ j (localizedFrozenAmplitudeSchwartz χ hχ hcχ a ha Φ hΦ q) z‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_compact_parameter_fiber_jet_bound
    (contDiff_localizedFrozenAmplitude hχ ha hΦ) hcχ.isCompact
    (hK.prod (isCompact_Icc.prod isCompact_Icc))
    (fun q _ => tsupport_localizedFrozenAmplitude_fiber_subset χ a Φ q) j
  exact ⟨C, hC, fun q hq hα hδ z => hb q ⟨hq, hα, hδ⟩ z⟩

end PlanarNikodym
