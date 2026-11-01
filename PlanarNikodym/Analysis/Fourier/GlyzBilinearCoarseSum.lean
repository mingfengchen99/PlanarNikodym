import PlanarNikodym.Analysis.Fourier.GlyzAsymmetricConstants
import PlanarNikodym.Analysis.Fourier.GlyzDyadicNestedBlocks

/-! Finite coarse-to-fine inequalities for the actual unweighted
bilinear integrals used in GLYZ Lemma 3.4. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace PlanarNikodym

theorem glyzDyadicSeparated_descendants {n q q' i j u v : ℕ}
    (hs : GlyzDyadicSeparated n n i j) (hu : u < 2 ^ q) (hv : v < 2 ^ q') :
    GlyzDyadicSeparated (n + q) (n + q') (i * 2 ^ q + u) (j * 2 ^ q' + v) := by
  have h₁ := glyzDyadicCenter_descendant_dist (n := n) (i := i) hu
  have h₂ := glyzDyadicCenter_descendant_dist (n := n) (i := j) hv
  have htri : |glyzDyadicCenter n i - glyzDyadicCenter n j| ≤
      |glyzDyadicCenter (n + q) (i * 2 ^ q + u) - glyzDyadicCenter n i| +
      |glyzDyadicCenter (n + q) (i * 2 ^ q + u) -
        glyzDyadicCenter (n + q') (j * 2 ^ q' + v)| +
      |glyzDyadicCenter (n + q') (j * 2 ^ q' + v) - glyzDyadicCenter n j| := by
    have h := abs_sub_le (glyzDyadicCenter n i)
      (glyzDyadicCenter (n + q) (i * 2 ^ q + u)) (glyzDyadicCenter n j)
    have h' := abs_sub_le (glyzDyadicCenter (n + q) (i * 2 ^ q + u))
      (glyzDyadicCenter (n + q') (j * 2 ^ q' + v)) (glyzDyadicCenter n j)
    rw [abs_sub_comm (glyzDyadicCenter n i)
      (glyzDyadicCenter (n + q) (i * 2 ^ q + u))] at h
    linarith
  unfold GlyzDyadicSeparated at hs ⊢
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def glyzBareBilinear (f g : E → ℂ) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ‖f x‖ₑ ^ a * ‖g x‖ₑ ^ b

theorem glyzBareBilinear_sum_le (s t : Finset ℕ) (f g : ℕ → SchwartzMap E ℂ)
    {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    glyzBareBilinear (fun x => ∑ i ∈ s, f i x) (fun x => ∑ j ∈ t, g j x) a b ≤
      (s.card : ℝ≥0∞) ^ (a - 1) * (t.card : ℝ≥0∞) ^ (b - 1) *
        ∑ i ∈ s, ∑ j ∈ t, glyzBareBilinear (f i) (g j) a b := by
  have hpoint (x : E) :
      ‖∑ i ∈ s, f i x‖ₑ ^ a * ‖∑ j ∈ t, g j x‖ₑ ^ b ≤
        ((s.card : ℝ≥0∞) ^ (a - 1) * (t.card : ℝ≥0∞) ^ (b - 1)) *
          ∑ i ∈ s, ∑ j ∈ t, ‖f i x‖ₑ ^ a * ‖g j x‖ₑ ^ b := by
    have hF := (ENNReal.rpow_le_rpow (enorm_sum_le s (fun i => f i x))
      (zero_le_one.trans ha)).trans (ENNReal.rpow_sum_le_const_mul_sum_rpow s _ ha)
    have hG := (ENNReal.rpow_le_rpow (enorm_sum_le t (fun j => g j x))
      (zero_le_one.trans hb)).trans (ENNReal.rpow_sum_le_const_mul_sum_rpow t _ hb)
    apply (mul_le_mul' hF hG).trans_eq
    rw [← Finset.sum_mul_sum]
    ring
  apply (lintegral_mono hpoint).trans_eq
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr ha) (by simp))
    (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr hb) (by simp)))]
  congr 1
  rw [lintegral_finsetSum s (fun i _ => Finset.measurable_sum t
    (fun j _ => ((f i).continuous.measurable.enorm.pow_const a).mul
      ((g j).continuous.measurable.enorm.pow_const b)))]
  apply Finset.sum_congr rfl
  intro i _
  exact lintegral_finsetSum t fun j _ =>
    ((f i).continuous.measurable.enorm.pow_const a).mul
      ((g j).continuous.measurable.enorm.pow_const b)

/-- A uniform bound for all fine pairs gives the coarse bound with
the explicit cardinality powers of Lemma 3.4. -/
theorem glyzBareBilinear_sum_le_uniform (s t : Finset ℕ) (f g : ℕ → SchwartzMap E ℂ)
    {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) {D : ℝ≥0∞}
    (hD : ∀ i ∈ s, ∀ j ∈ t, glyzBareBilinear (f i) (g j) a b ≤ D) :
    glyzBareBilinear (fun x => ∑ i ∈ s, f i x) (fun x => ∑ j ∈ t, g j x) a b ≤
      (s.card : ℝ≥0∞) ^ a * (t.card : ℝ≥0∞) ^ b * D := by
  apply (glyzBareBilinear_sum_le s t f g ha hb).trans
  have hsum : (∑ i ∈ s, ∑ j ∈ t, glyzBareBilinear (f i) (g j) a b) ≤
      (s.card : ℝ≥0∞) * (t.card : ℝ≥0∞) * D := by
    apply (Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hD i hi j hj).trans_eq
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  apply (mul_le_mul_right hsum _).trans_eq
  have hs : (s.card : ℝ≥0∞) ^ (a - 1) * s.card = (s.card : ℝ≥0∞) ^ a := by
    calc
      _ = (s.card : ℝ≥0∞) ^ (a - 1) * (s.card : ℝ≥0∞) ^ (1 : ℝ) := by
        rw [ENNReal.rpow_one]
      _ = (s.card : ℝ≥0∞) ^ ((a - 1) + 1) :=
        (ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.mpr ha) zero_le_one).symm
      _ = _ := by congr 1; ring
  have ht : (t.card : ℝ≥0∞) ^ (b - 1) * t.card = (t.card : ℝ≥0∞) ^ b := by
    calc
      _ = (t.card : ℝ≥0∞) ^ (b - 1) * (t.card : ℝ≥0∞) ^ (1 : ℝ) := by
        rw [ENNReal.rpow_one]
      _ = (t.card : ℝ≥0∞) ^ ((b - 1) + 1) :=
        (ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.mpr hb) zero_le_one).symm
      _ = _ := by congr 1; ring
  calc
    _ = ((s.card : ℝ≥0∞) ^ (a - 1) * s.card) *
      ((t.card : ℝ≥0∞) ^ (b - 1) * t.card) * D := by ring
    _ = _ := by rw [hs, ht]

theorem glyzBareBilinear_le_weighted (μ ν : Measure E) [SFinite μ] [SFinite ν]
    (f g : SchwartzMap E ℂ) (a b : ℝ) (K L : ℝ≥0∞) (hK : K ≠ ⊤) (hL : L ≠ ⊤)
    (hf : ∀ x, ‖f x‖ₑ ^ a ≤ K * glyzPowerAverage μ f a x)
    (hg : ∀ x, ‖g x‖ₑ ^ b ≤ L * glyzPowerAverage ν g b x) :
    glyzBareBilinear f g a b ≤ K * L * glyzWeightedBilinear μ ν f g a b := by
  apply (lintegral_mono fun x => mul_le_mul' (hf x) (hg x)).trans_eq
  have he (x : E) : K * glyzPowerAverage μ f a x * (L * glyzPowerAverage ν g b x) =
      (K * L) * (glyzPowerAverage μ f a x * glyzPowerAverage ν g b x) := by ring
  simp_rw [he]
  exact lintegral_const_mul' _ _ (ENNReal.mul_ne_top hK hL)

end PlanarNikodym
