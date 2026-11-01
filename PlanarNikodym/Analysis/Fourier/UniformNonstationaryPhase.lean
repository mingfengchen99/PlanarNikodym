import PlanarNikodym.Analysis.Fourier.NonstationaryPhase
import PlanarNikodym.Analysis.Jets.CutoffGraphJetBounds

/-! Parameter-uniform nonstationary phase. Joint compactness supplies
the constants; the recursive amplitudes are the actual integration by
parts amplitudes. The joint phase only has to be smooth at the support
of the initial amplitude. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace PlanarNikodym

def partialTimeDeriv {P E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : P × ℝ → E) (x : P × ℝ) : E := deriv (fun t => F (x.1, t)) x.2

theorem contDiffAt_partialTimeDeriv
    {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : P × ℝ → E} {x : P × ℝ} (hF : ContDiffAt ℝ ∞ F x) :
    ContDiffAt ℝ ∞ (partialTimeDeriv F) x := by
  let H : ℝ × P → E := fun y => F (y.2, y.1)
  have hH : ContDiffAt ℝ ∞ H (x.2, x.1) :=
    hF.comp (x.2, x.1) (contDiffAt_snd.prodMk contDiffAt_fst)
  have hD := contDiffAt_fiber_fderiv hH
  have hSwap : ContDiffAt ℝ ∞ (fun y : P × ℝ => (y.2, y.1)) x :=
    contDiffAt_snd.prodMk contDiffAt_fst
  have hpartial : ContDiffAt ℝ ∞
      (fun y : P × ℝ => fderiv ℝ (fun t => F (y.1, t)) y.2) x := by
    simpa only [H, Function.comp_def] using
      hD.comp (f := fun y : P × ℝ => (y.2, y.1)) x hSwap
  exact (ContinuousLinearMap.apply ℝ E (1 : ℝ)).contDiff.contDiffAt.comp x
    hpartial

theorem contDiff_partialTimeDeriv
    {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (partialTimeDeriv F) :=
  contDiff_iff_contDiffAt.mpr (fun _ => contDiffAt_partialTimeDeriv hF.contDiffAt)

theorem tsupport_partialTimeDeriv_subset
    {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : P × ℝ → E) :
    tsupport (partialTimeDeriv F) ⊆ tsupport F := by
  apply closure_minimal ?_ (isClosed_tsupport F)
  intro x hx
  by_contra h
  have he : (fun t => F (x.1, t)) =ᶠ[𝓝 x.2] fun _ => 0 :=
    (notMem_tsupport_iff_eventuallyEq.mp h).comp_tendsto
      (continuous_const.prodMk continuous_id).continuousAt
  have hz : partialTimeDeriv F x = 0 := by
    simpa only [partialTimeDeriv, deriv_const] using he.deriv_eq
  exact hx hz

def parameterNonstationaryQuotient {P : Type}
    (Φ : P × ℝ → ℝ) (a : P × ℝ → ℂ) (x : P × ℝ) : ℂ :=
  a x / ((partialTimeDeriv Φ x : ℝ) : ℂ)

theorem tsupport_parameterNonstationaryQuotient_subset
    {P : Type} [TopologicalSpace P] (Φ : P × ℝ → ℝ) (a : P × ℝ → ℂ) :
    tsupport (parameterNonstationaryQuotient Φ a) ⊆ tsupport a := by
  change tsupport (fun x => a x / ((partialTimeDeriv Φ x : ℝ) : ℂ)) ⊆ tsupport a
  simp only [div_eq_mul_inv]
  exact tsupport_mul_subset_left

theorem contDiff_parameterNonstationaryQuotient
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Φ : P × ℝ → ℝ} {a : P × ℝ → ℂ}
    (hΦ : ∀ x ∈ tsupport a, ContDiffAt ℝ ∞ Φ x) (ha : ContDiff ℝ ∞ a)
    (hne : ∀ x ∈ tsupport a, partialTimeDeriv Φ x ≠ 0) :
    ContDiff ℝ ∞ (parameterNonstationaryQuotient Φ a) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport a
  · have hD : ContDiffAt ℝ ∞ (fun y => ((partialTimeDeriv Φ y : ℝ) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x (contDiffAt_partialTimeDeriv (hΦ x hx))
    change ContDiffAt ℝ ∞
      (fun y : P × ℝ => a y / (((partialTimeDeriv Φ y : ℝ) : ℂ))) x
    simp only [div_eq_mul_inv]
    exact ha.contDiffAt.mul (hD.inv (by exact_mod_cast hne x hx))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp only [Pi.zero_apply] at hy
    simp only [parameterNonstationaryQuotient, hy, zero_div]

def parameterNonstationaryTransfer {P : Type}
    (Φ : P × ℝ → ℝ) (a : P × ℝ → ℂ) (x : P × ℝ) : ℂ :=
  -partialTimeDeriv (parameterNonstationaryQuotient Φ a) x

theorem tsupport_parameterNonstationaryTransfer_subset
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : P × ℝ → ℝ) (a : P × ℝ → ℂ) :
    tsupport (parameterNonstationaryTransfer Φ a) ⊆ tsupport a := by
  calc
    _ = tsupport (partialTimeDeriv (parameterNonstationaryQuotient Φ a)) :=
      tsupport_neg _
    _ ⊆ tsupport (parameterNonstationaryQuotient Φ a) :=
      tsupport_partialTimeDeriv_subset _
    _ ⊆ _ := tsupport_parameterNonstationaryQuotient_subset Φ a

theorem contDiff_parameterNonstationaryTransfer
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Φ : P × ℝ → ℝ} {a : P × ℝ → ℂ}
    (hΦ : ∀ x ∈ tsupport a, ContDiffAt ℝ ∞ Φ x) (ha : ContDiff ℝ ∞ a)
    (hne : ∀ x ∈ tsupport a, partialTimeDeriv Φ x ≠ 0) :
    ContDiff ℝ ∞ (parameterNonstationaryTransfer Φ a) :=
  (contDiff_partialTimeDeriv (contDiff_parameterNonstationaryQuotient hΦ ha hne)).neg

/-- The same recursive amplitude as the one-dimensional integration by
parts theorem, now viewed as one joint parameter-time function. -/
def parameterNonstationaryAmplitude {P : Type}
    (Φ : P × ℝ → ℝ) (a : P × ℝ → ℂ) (n : ℕ) (x : P × ℝ) : ℂ :=
  nonstationaryAmplitude (fun t => Φ (x.1, t)) (fun t => a (x.1, t)) n x.2

@[simp] theorem parameterNonstationaryAmplitude_zero {P : Type}
    (Φ : P × ℝ → ℝ) (a : P × ℝ → ℂ) :
    parameterNonstationaryAmplitude Φ a 0 = a := rfl

@[simp] theorem parameterNonstationaryAmplitude_succ {P : Type}
    (Φ : P × ℝ → ℝ) (a : P × ℝ → ℂ) (n : ℕ) :
    parameterNonstationaryAmplitude Φ a (n + 1) =
      parameterNonstationaryTransfer Φ (parameterNonstationaryAmplitude Φ a n) := rfl

theorem tsupport_parameterNonstationaryAmplitude_subset
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : P × ℝ → ℝ) (a : P × ℝ → ℂ) (n : ℕ) :
    tsupport (parameterNonstationaryAmplitude Φ a n) ⊆ tsupport a := by
  induction n with
  | zero => exact Subset.rfl
  | succ n ih =>
    rw [parameterNonstationaryAmplitude_succ]
    exact (tsupport_parameterNonstationaryTransfer_subset Φ _).trans ih

theorem contDiff_parameterNonstationaryAmplitude
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Φ : P × ℝ → ℝ} {a : P × ℝ → ℂ}
    (hΦ : ∀ x ∈ tsupport a, ContDiffAt ℝ ∞ Φ x) (ha : ContDiff ℝ ∞ a)
    (hne : ∀ x ∈ tsupport a, partialTimeDeriv Φ x ≠ 0) (n : ℕ) :
    ContDiff ℝ ∞ (parameterNonstationaryAmplitude Φ a n) := by
  induction n with
  | zero => exact ha
  | succ n ih =>
    rw [parameterNonstationaryAmplitude_succ]
    exact contDiff_parameterNonstationaryTransfer
      (fun x hx => hΦ x (tsupport_parameterNonstationaryAmplitude_subset Φ a n hx)) ih
      (fun x hx => hne x (tsupport_parameterNonstationaryAmplitude_subset Φ a n hx))

theorem hasCompactSupport_parameterNonstationaryAmplitude
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : P × ℝ → ℝ) {a : P × ℝ → ℂ} (hc : HasCompactSupport a) (n : ℕ) :
    HasCompactSupport (parameterNonstationaryAmplitude Φ a n) :=
  hc.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_parameterNonstationaryAmplitude_subset Φ a n)

/-- Joint compact support and actual recursive smoothness provide one
decay constant for every parameter and every nonzero oscillation frequency. -/
theorem exists_uniform_nonstationary_decay_constant
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Φ : P × ℝ → ℝ} {a : P × ℝ → ℂ}
    (hΦ : ∀ x ∈ tsupport a, ContDiffAt ℝ ∞ Φ x)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hne : ∀ x ∈ tsupport a, partialTimeDeriv Φ x ≠ 0) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : P) (r : ℝ), r ≠ 0 →
      ‖∫ t : ℝ, phaseOscillation (fun s => Φ (p, s)) r t * a (p, t)‖ ≤
        C * (|r|⁻¹) ^ n := by
  classical
  let B := parameterNonstationaryAmplitude Φ a n
  have hBc : HasCompactSupport B := hasCompactSupport_parameterNonstationaryAmplitude Φ hc n
  have hB : ContDiff ℝ ∞ B := contDiff_parameterNonstationaryAmplitude hΦ ha hne n
  obtain ⟨x₀, hx₀⟩ := hB.continuous.norm.exists_forall_ge_of_hasCompactSupport hBc.norm
  let M : ℝ := ‖B x₀‖
  have hM : 0 ≤ M := norm_nonneg _
  let T : Set ℝ := Prod.snd '' tsupport a
  have hT : IsCompact T := hc.isCompact.image continuous_snd
  let C : ℝ := M * volume.real T
  have hC : 0 ≤ C := mul_nonneg hM (by positivity)
  refine ⟨C, hC, ?_⟩
  intro p r hr
  have hslice : tsupport (fun t : ℝ => a (p, t)) ⊆
      (fun t : ℝ => (p, t)) ⁻¹' tsupport a :=
    tsupport_comp_subset_preimage a (continuous_const.prodMk continuous_id)
  have hsliceT : tsupport (fun t : ℝ => a (p, t)) ⊆ T := by
    intro t ht
    exact ⟨(p, t), hslice ht, rfl⟩
  have hca : HasCompactSupport (fun t : ℝ => a (p, t)) :=
    hT.of_isClosed_subset (isClosed_tsupport _) hsliceT
  have hΦp : ∀ t ∈ tsupport (fun t : ℝ => a (p, t)),
      ContDiffAt ℝ ∞ (fun t : ℝ => Φ (p, t)) t := by
    intro t ht
    exact (hΦ (p, t) (hslice ht)).comp
      (f := fun t : ℝ => (p, t)) t (contDiffAt_const.prodMk contDiffAt_id)
  have hap : ContDiff ℝ ∞ (fun t : ℝ => a (p, t)) :=
    ha.comp (contDiff_const.prodMk contDiff_id)
  have hnep : ∀ t ∈ tsupport (fun t : ℝ => a (p, t)),
      deriv (fun s => Φ (p, s)) t ≠ 0 := fun t ht => hne (p, t) (hslice ht)
  have hBi : Integrable (fun t : ℝ => ‖B (p, t)‖) :=
    (integrable_nonstationaryAmplitude hΦp hap hca hnep n).norm
  have hI : (∫ t : ℝ, ‖B (p, t)‖) ≤ C := by
    have hi : Integrable (T.indicator (fun _ => M)) :=
      (integrableOn_const hT.measure_ne_top).integrable_indicator hT.measurableSet
    calc
      _ ≤ ∫ t : ℝ, T.indicator (fun _ => M) t := by
        apply integral_mono hBi hi
        intro t
        by_cases ht : t ∈ T
        · simpa only [indicator_of_mem ht, M] using hx₀ (p, t)
        · have hx : (p, t) ∉ tsupport B := by
            intro hx
            exact ht ⟨(p, t), tsupport_parameterNonstationaryAmplitude_subset Φ a n hx, rfl⟩
          simp only [image_eq_zero_of_notMem_tsupport hx, norm_zero, indicator_of_notMem ht,
            le_refl]
      _ = C := by rw [integral_indicator_const _ hT.measurableSet, smul_eq_mul]; dsimp [C]; ring
  calc
    _ ≤ (|r|⁻¹) ^ n * ∫ t : ℝ, ‖B (p, t)‖ :=
      norm_phaseOscillation_integral_le hΦp hap hca hnep hr n
    _ ≤ (|r|⁻¹) ^ n * C := mul_le_mul_of_nonneg_left hI (by positivity)
    _ = _ := mul_comm _ _

end PlanarNikodym
