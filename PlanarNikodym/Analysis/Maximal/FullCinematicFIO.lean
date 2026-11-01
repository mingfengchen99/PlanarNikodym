import PlanarNikodym.Analysis.Maximal.CinematicRetainedFIO
import PlanarNikodym.Analysis.Maximal.E2FIOAmplitudePartition

/-! Finite localization of the entire compact cinematic FIO amplitude.
The resulting estimate includes the original parameter volume and all time
frequencies in the amplitude; its constant precedes frequency and input. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace PlanarNikodym

theorem exists_finite_complex_amplitude_partition
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {a : E → ℂ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (U : ι → Set E) (hU : ∀ i, IsOpen (U i)) (hcover : tsupport a ⊆ ⋃ i, U i) :
    ∃ (S : Finset ι) (b : S → E → ℂ),
      (∀ i, ContDiff ℝ ∞ (b i) ∧ HasCompactSupport (b i) ∧ tsupport (b i) ⊆ U i) ∧
      ∀ z, ∑ i : S, b i z = a z := by
  classical
  obtain ⟨S,hS⟩ := hc.isCompact.elim_finite_subcover U hU hcover
  have hcoverS : tsupport a ⊆ ⋃ i : S, U i := by
    intro z hz
    obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp (hS hz)
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,hzi⟩
  obtain ⟨b,hb,hsum⟩ := e2_exists_complex_amplitude_partition ha hc
    (fun i : S => U i) (fun i => hU i) hcoverS
  exact ⟨S,b,hb,hsum⟩

variable {Q : Type*} [NormedAddCommGroup Q] [MeasurableSpace Q] [BorelSpace Q]

theorem stronglyMeasurable_fullFIO_of_continuous
    {Φ : Q × Plane → ℝ} {a : Q × Plane → ℂ}
    (hΦ : Continuous Φ) (ha : Continuous a) {f : Plane → ℂ} (hf : Continuous f) (r : ℝ) :
    StronglyMeasurable (e2FullFIOIntegral r (fun q x => Φ (q,x)) a f) := by
  have hK : Continuous (fun z : Q × Plane =>
      e2FIOAmplitudeKernel r (fun q x => Φ (q,x)) a z.1 z.2 * f z.2) :=
    ((Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (continuous_const.mul hΦ)).mul continuous_const)).mul ha).mul (hf.comp continuous_snd)
  exact hK.stronglyMeasurable.integral_prod_right'

omit [MeasurableSpace Q] [BorelSpace Q] in
theorem integrable_fullFIO_input_of_continuous
    {Φ : Q × Plane → ℝ} {a : Q × Plane → ℂ}
    (hΦ : Continuous Φ) (ha : Continuous a) (hc : HasCompactSupport a)
    {f : Plane → ℂ} (hf : Continuous f) (r : ℝ) (q : Q) :
    Integrable (fun x : Plane => e2FIOAmplitudeKernel r (fun q x => Φ (q,x)) a q x * f x) := by
  have hcont : Continuous (fun x : Plane =>
      e2FIOAmplitudeKernel r (fun q x => Φ (q,x)) a q x * f x) :=
    ((Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (continuous_const.mul (hΦ.comp (continuous_const.prodMk continuous_id)))).mul
        continuous_const)).mul (ha.comp (continuous_const.prodMk continuous_id))).mul hf
  apply hcont.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (hc.isCompact.image continuous_snd)
  intro x hx
  have hz : a (q,x) = 0 := by
    by_contra hn
    exact hx ⟨(q,x),subset_tsupport a hn,rfl⟩
  simp [e2FIOAmplitudeKernel,hz]

theorem Family.exists_cinematic_full_fio_L2_bound {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    {a : Parameters 2 d × Plane → ℂ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hdet : ∀ z ∈ tsupport a, G.cinematicDet (z.2.1,z.1) ≠ 0)
    (hη : ∀ z ∈ tsupport a, z.2.2 ≠ 0) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ r : ℝ, 0 < r → ∀ f : Plane → ℂ, Continuous f →
      eLpNorm (e2FullFIOIntegral r (fun q x => x.2 * G.γ x.1 q) a f) 2 volume ≤
        C * ENNReal.ofReal r⁻¹ * eLpNorm f 2 volume := by
  classical
  have hlocal (z : tsupport a) :=
    G.exists_local_cinematic_full_fio_L2_bound hG z.1.1 z.1.2 (hη z z.2) (hdet z z.2)
  choose U hU hz hbound using hlocal
  have hcover : tsupport a ⊆ ⋃ z : tsupport a, U z :=
    fun z hza => mem_iUnion.mpr ⟨⟨z,hza⟩,hz ⟨z,hza⟩⟩
  obtain ⟨S,b,hb,hsum⟩ := exists_finite_complex_amplitude_partition ha hc U hU hcover
  have hex (i : S) := hbound i (b i) (hb i).1 (hb i).2.1 (hb i).2.2
  choose C hC hest using hex
  refine ⟨∑ i : S, C i, ENNReal.sum_ne_top.mpr (fun i _ => hC i),?_⟩
  intro r hr f hf
  let Φ : Parameters 2 d × Plane → ℝ := fun z => z.2.2 * G.γ z.2.1 z.1
  have hΦ : Continuous Φ := continuous_snd.snd.mul
    (hG.continuous.comp (continuous_snd.fst.prodMk continuous_fst))
  have hint (i : S) (q : Parameters 2 d) :=
    integrable_fullFIO_input_of_continuous hΦ (hb i).1.continuous (hb i).2.1 hf r q
  have heq : e2FullFIOIntegral r (fun q x => x.2 * G.γ x.1 q) a f =
      ∑ i : S, e2FullFIOIntegral r (fun q x => x.2 * G.γ x.1 q) (b i) f := by
    funext q
    simp only [Finset.sum_apply,e2FullFIOIntegral]
    rw [← integral_finsetSum _ (fun i _ => hint i q)]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [e2FIOAmplitudeKernel,← Finset.sum_mul,← Finset.mul_sum,hsum]
    rfl
  rw [heq]
  calc
    _ ≤ ∑ i : S, eLpNorm (e2FullFIOIntegral r
        (fun q x => x.2 * G.γ x.1 q) (b i) f) 2 volume :=
      eLpNorm_sum_le (fun i _ => (stronglyMeasurable_fullFIO_of_continuous hΦ
        (hb i).1.continuous hf r).aestronglyMeasurable) (by norm_num)
    _ ≤ ∑ i : S, C i * ENNReal.ofReal r⁻¹ * eLpNorm f 2 volume :=
      Finset.sum_le_sum (fun i _ => hest i r hr f hf)
    _ = _ := by rw [← Finset.sum_mul,← Finset.sum_mul]

end PlanarNikodym
