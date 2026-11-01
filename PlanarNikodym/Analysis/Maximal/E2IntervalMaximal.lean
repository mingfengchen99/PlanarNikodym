import PlanarNikodym.Analysis.Maximal.E2CompactFiberMaximal
import PlanarNikodym.Analysis.Maximal.E2ContinuousMaximal
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Definition 1.3 on the original closed time interval and an arbitrary
compact parameter set. The two endpoints do not affect the integral. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

def Family.intervalAverage_e2 {d : ℕ} (G : Family 2 d) (f : Plane → ℂ)
    (q : Parameters 2 d) : ℂ := ∫ t in G.I.carrier, f (G.graphMap q t)

def Family.intervalMaximal_e2 {d : ℕ} (G : Family 2 d) (K : Set (Parameters 2 d))
    (f : Plane → ℂ) (z : Base 2) : ℝ≥0∞ :=
  ⨆ u : Aux d, ⨆ (_ : (z, u) ∈ K), ‖G.intervalAverage_e2 f (z, u)‖ₑ

theorem Family.intervalAverage_e2_eq_open_interval {d : ℕ} (G : Family 2 d)
    (f : Plane → ℂ) (q : Parameters 2 d) :
    G.intervalAverage_e2 f q = ∫ t in Ioo G.I.left G.I.right, f (G.graphMap q t) :=
  integral_Icc_eq_integral_Ioo

theorem Family.intervalMaximal_e2_eq_open_interval {d : ℕ} (G : Family 2 d)
    (K : Set (Parameters 2 d)) (f : Plane → ℂ) (z : Base 2) :
    G.intervalMaximal_e2 K f z =
      ⨆ u : Aux d, ⨆ (_ : (z, u) ∈ K),
        ‖∫ t in Ioo G.I.left G.I.right, f (G.graphMap (z, u) t)‖ₑ := by
  unfold intervalMaximal_e2
  simp_rw [G.intervalAverage_e2_eq_open_interval]

theorem Family.intervalIntegrand_e2_integrable {d : ℕ} (G : Family 2 d)
    (hG : G.IsSmooth) {f : Plane → ℂ} (hf : Continuous f)
    {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) {q : Parameters 2 d} (hq : q ∈ G.W) :
    IntegrableOn (fun t => f (G.graphMap q t)) G.I.carrier := by
  have hc : ContinuousOn (fun t => f (G.graphMap q t)) G.I.carrier := by
    apply hf.comp_continuousOn
    apply continuousOn_id.prodMk
    exact hG.continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
      (fun t ht => ⟨ht, hq⟩)
  apply (integrableOn_const (C := B) isCompact_Icc.measure_lt_top.ne).mono'
    (hc.aestronglyMeasurable measurableSet_Icc)
  exact Filter.Eventually.of_forall (fun t => hB _)

theorem Family.continuousOn_intervalAverage_e2 {d : ℕ} (G : Family 2 d)
    (hG : G.IsSmooth) {f : Plane → ℂ} (hf : Continuous f)
    {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) : ContinuousOn (G.intervalAverage_e2 f) G.W := by
  apply continuousOn_of_dominated (bound := fun _ => B)
  · intro q hq
    exact (G.intervalIntegrand_e2_integrable hG hf hB hq).aestronglyMeasurable
  · intro q _
    exact Filter.Eventually.of_forall (fun t => hB _)
  · exact integrableOn_const isCompact_Icc.measure_lt_top.ne
  · filter_upwards [ae_restrict_mem (show MeasurableSet G.I.carrier from measurableSet_Icc)]
      with t ht
    apply hf.comp_continuousOn
    apply continuousOn_const.prodMk
    exact hG.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
      (fun q hq => ⟨ht, hq⟩)

theorem Family.upperSemicontinuous_intervalMaximal_e2 {d : ℕ} (G : Family 2 d)
    (hG : G.IsSmooth) (K : Set (Parameters 2 d)) (hK : IsCompact K) (hKW : K ⊆ G.W)
    {f : Plane → ℂ} (hf : Continuous f) {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) :
    UpperSemicontinuous (G.intervalMaximal_e2 K f) :=
  e2_upperSemicontinuous_compact_fiber_sup K hK (fun q => ‖G.intervalAverage_e2 f q‖ₑ)
    (((G.continuousOn_intervalAverage_e2 hG hf hB).mono hKW).enorm)

theorem Family.measurable_intervalMaximal_e2 {d : ℕ} (G : Family 2 d)
    (hG : G.IsSmooth) (K : Set (Parameters 2 d)) (hK : IsCompact K) (hKW : K ⊆ G.W)
    {f : Plane → ℂ} (hf : Continuous f) {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) :
    Measurable (G.intervalMaximal_e2 K f) :=
  (G.upperSemicontinuous_intervalMaximal_e2 hG K hK hKW hf hB).measurable

theorem Family.intervalMaximal_e2_ne_top {d : ℕ} (G : Family 2 d)
    (K : Set (Parameters 2 d)) {f : Plane → ℂ} {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B)
    (z : Base 2) : G.intervalMaximal_e2 K f z ≠ ⊤ := by
  have hI : volume G.I.carrier < ⊤ := isCompact_Icc.measure_lt_top
  apply ne_top_of_le_ne_top (ENNReal.mul_ne_top hI.ne
    ENNReal.ofReal_ne_top)
  apply iSup_le
  intro u
  apply iSup_le
  intro _
  calc
    _ ≤ ∫⁻ t in G.I.carrier, ‖f (G.graphMap (z, u) t)‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ _ in G.I.carrier, ENNReal.ofReal B := by
      apply lintegral_mono
      intro t
      dsimp only
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hB _)
    _ = volume G.I.carrier * ENNReal.ofReal B := by simp [mul_comm]

theorem Family.intervalMaximal_e2_LInfinity {d : ℕ} (G : Family 2 d)
    (K : Set (Parameters 2 d)) {f : Plane → ℂ} (hf : Continuous f) :
    eLpNorm (G.intervalMaximal_e2 K f) ⊤ volume ≤ volume G.I.carrier * eLpNorm f ⊤ volume := by
  have hclosed : IsClosed {x | ‖f x‖ₑ ≤ eLpNorm f ⊤ volume} :=
    isClosed_le hf.enorm continuous_const
  have he : {x | ‖f x‖ₑ ≤ eLpNorm f ⊤ volume} = univ := by
    apply (hclosed.ae_eq_univ_iff_eq (μ := volume)).mp
    rw [ae_eq_univ]
    exact enorm_ae_le_eLpNormEssSup f volume
  have hpoint (x : Plane) : ‖f x‖ₑ ≤ eLpNorm f ⊤ volume := by
    have hx : x ∈ ({x | ‖f x‖ₑ ≤ eLpNorm f ⊤ volume} : Set Plane) := he ▸ mem_univ x
    exact hx
  apply eLpNormEssSup_le_of_ae_enorm_bound
  filter_upwards [] with z
  rw [enorm_eq_self]
  apply iSup_le
  intro u
  apply iSup_le
  intro _
  calc
    _ ≤ ∫⁻ t in G.I.carrier, ‖f (G.graphMap (z, u) t)‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ _ in G.I.carrier, eLpNorm f ⊤ volume := lintegral_mono (fun t => hpoint _)
    _ = _ := by simp [mul_comm]

end PlanarNikodym
