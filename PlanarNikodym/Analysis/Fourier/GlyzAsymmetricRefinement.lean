import PlanarNikodym.Analysis.Fourier.GlyzAsymmetricConstants
import PlanarNikodym.Analysis.Fourier.GlyzDyadicNestedBlocks

/-! The exact square-energy algebra for passing a lower-degree integral
gain to the actual optimal asymmetric constant. Every child energy
belongs to the same original Schwartz family. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal BigOperators
namespace PlanarNikodym

theorem glyzDyadicSeparated_refine_left {n n' q i j u : ℕ}
    (hs : GlyzDyadicSeparated n n' i j) (hu : u < 2 ^ q) :
    GlyzDyadicSeparated (n + q) n' (i * 2 ^ q + u) j := by
  have hd := glyzDyadicCenter_descendant_dist (n := n) (i := i) hu
  have ht := abs_sub_le (glyzDyadicCenter n i)
    (glyzDyadicCenter (n + q) (i * 2 ^ q + u)) (glyzDyadicCenter n' j)
  rw [abs_sub_comm (glyzDyadicCenter n i)
    (glyzDyadicCenter (n + q) (i * 2 ^ q + u))] at ht
  unfold GlyzDyadicSeparated at hs ⊢
  linarith

theorem glyz_refinement_energy_power {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    {a B V : ℝ} (ha : 0 < a) (hB : 0 ≤ B) (hV : 0 ≤ V) :
    (∑ i ∈ s, (B * (w i ^ (a / 2) * V)) ^ (2 / a)) ^ (a / 2) =
      B * ((∑ i ∈ s, w i) ^ (a / 2) * V) := by
  have hexp : a / 2 * (2 / a) = 1 := by field_simp
  have hexp' : 2 / a * (a / 2) = 1 := by field_simp
  have hterm (i : ι) (hi : i ∈ s) :
      (B * (w i ^ (a / 2) * V)) ^ (2 / a) =
        (B * V) ^ (2 / a) * w i := by
    rw [show B * (w i ^ (a / 2) * V) = (B * V) * w i ^ (a / 2) by ring,
      Real.mul_rpow (mul_nonneg hB hV) (Real.rpow_nonneg (hw i hi) _),
      ← Real.rpow_mul (hw i hi), hexp, Real.rpow_one]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    Real.mul_rpow (Real.rpow_nonneg (mul_nonneg hB hV) _)
      (Finset.sum_nonneg hw),
    ← Real.rpow_mul (mul_nonneg hB hV), hexp', Real.rpow_one]
  ring

theorem glyzDyadicBilinearEnergy_refine (m N n n' q : ℕ) (p : ℝ≥0)
    {a B : ℝ} (ha : 0 < a) (hB : 0 ≤ B)
    (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) (i j : ℕ) (hq : n + q ≤ N) :
    (∑ u ∈ Finset.range (2 ^ q),
      (B * glyzDyadicBilinearEnergy m N (n + q) n' p a f (i * 2 ^ q + u) j) ^
        (2 / a)) ^ (a / 2) =
      B * glyzDyadicBilinearEnergy m N n n' p a f i j := by
  unfold glyzDyadicBilinearEnergy
  rw [glyz_refinement_energy_power _ _
    (fun u _ => glyz_dyadic_square_block_nonneg m N (n + q) (i * 2 ^ q + u) p f)
    ha hB (Real.rpow_nonneg (glyz_dyadic_square_block_nonneg m N n' j p f) _)]
  rw [← glyzDyadicBlock_refine _ N n q i hq]

/-- The original nonnegative integral inequality passes to real
constants only after all child integrals have been proved finite. -/
theorem glyz_asymmetric_refinement_real_of_ennreal
    {m A N n n' q : ℕ} (hA : m < A) (p : ℝ≥0) (hp : 0 < p)
    {a D : ℝ} (ha : 0 < a) (hap : a ≤ (p : ℝ)) (hD : 0 ≤ D)
    (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) (i j : ℕ)
    (hgain :
      glyzWeightedBilinear (glyzDyadicPolarMeasure m A n i)
        (glyzDyadicPolarMeasure m A n' j)
        (glyzDyadicBlock f N n i : SchwartzMap (GlyzSpace m) ℂ)
        (glyzDyadicBlock f N n' j : SchwartzMap (GlyzSpace m) ℂ) a ((p : ℝ) - a) ≤
      ENNReal.ofReal D *
        (∑ u ∈ Finset.range (2 ^ q),
          (glyzWeightedBilinear (glyzDyadicPolarMeasure m A (n + q) (i * 2 ^ q + u))
            (glyzDyadicPolarMeasure m A n' j)
            (glyzDyadicBlock f N (n + q) (i * 2 ^ q + u) : SchwartzMap (GlyzSpace m) ℂ)
            (glyzDyadicBlock f N n' j : SchwartzMap (GlyzSpace m) ℂ) a ((p : ℝ) - a)) ^
              (2 / a)) ^ (a / 2)) :
    glyzDyadicBilinearValue m A N n n' p a f i j ≤
      D * (∑ u ∈ Finset.range (2 ^ q),
        glyzDyadicBilinearValue m A N (n + q) n' p a f (i * 2 ^ q + u) j ^
          (2 / a)) ^ (a / 2) := by
  let V (u : ℕ) := glyzWeightedBilinear
    (glyzDyadicPolarMeasure m A (n + q) (i * 2 ^ q + u))
    (glyzDyadicPolarMeasure m A n' j)
    (glyzDyadicBlock f N (n + q) (i * 2 ^ q + u) : SchwartzMap (GlyzSpace m) ℂ)
    (glyzDyadicBlock f N n' j : SchwartzMap (GlyzSpace m) ℂ) a ((p : ℝ) - a)
  have hfinite (u : ℕ) : V u ≠ ⊤ :=
    (glyz_polar_bilinear_lt_top hA _ _ _ _ (show (0 : ℝ) < p from hp) ha.le hap).ne
  have hterms (u : ℕ) : V u ^ (2 / a) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) (hfinite u)
  have hsum : (∑ u ∈ Finset.range (2 ^ q), V u ^ (2 / a)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun u _ => hterms u
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hsum)) hgain
  change glyzDyadicBilinearValue m A N n n' p a f i j ≤
    (ENNReal.ofReal D * (∑ u ∈ Finset.range (2 ^ q), V u ^ (2 / a)) ^ (a / 2)).toReal at h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD, ← ENNReal.toReal_rpow,
    ENNReal.toReal_sum (fun u _ => hterms u)] at h
  simpa only [← ENNReal.toReal_rpow, V, glyzDyadicBilinearValue] using h

/-- This is the optimization step, separated from the analytic proof
of the displayed integral gain. The actual GL5 theorem supplies that
gain when this lemma is applied. -/
theorem glyzAsymmetricIntegralConstant_le_of_refinement
    {m A N n n' q : ℕ} (hA : m < A) (p : ℝ≥0) (hp : 1 ≤ p)
    {a D : ℝ} (ha : 0 < a) (hap : a ≤ (p : ℝ)) (hD : 0 ≤ D)
    (hq : n + q ≤ N)
    (hgain : ∀ f : ℕ → SchwartzMap (GlyzSpace m) ℂ, GlyzDyadicSupported m N f →
      ∀ i < 2 ^ n, ∀ j < 2 ^ n', GlyzDyadicSeparated n n' i j →
        glyzDyadicBilinearValue m A N n n' p a f i j ≤
          D * (∑ u ∈ Finset.range (2 ^ q),
            glyzDyadicBilinearValue m A N (n + q) n' p a f (i * 2 ^ q + u) j ^
              (2 / a)) ^ (a / 2)) :
    glyzAsymmetricIntegralConstant m A N n n' p a ≤
      D * glyzAsymmetricIntegralConstant m A N (n + q) n' p a := by
  let B := glyzAsymmetricIntegralConstant m A N (n + q) n' p a
  have hB : 0 ≤ B := glyzAsymmetricIntegralConstant_nonneg hA N _ _ p hp ha.le hap
  apply glyzAsymmetricIntegralConstant_le
  refine ⟨mul_nonneg hD hB, fun f hf i hi j hj hs => ?_⟩
  have hsum :
      (∑ u ∈ Finset.range (2 ^ q),
        glyzDyadicBilinearValue m A N (n + q) n' p a f (i * 2 ^ q + u) j ^ (2 / a)) ≤
      ∑ u ∈ Finset.range (2 ^ q),
        (B * glyzDyadicBilinearEnergy m N (n + q) n' p a f (i * 2 ^ q + u) j) ^
          (2 / a) := by
    apply Finset.sum_le_sum
    intro u hu
    have hu' := Finset.mem_range.mp hu
    have hi' : i * 2 ^ q + u < 2 ^ (n + q) := by
      rw [pow_add]
      nlinarith [Nat.mul_le_mul_right (2 ^ q) hi]
    exact Real.rpow_le_rpow ENNReal.toReal_nonneg
      ((glyzAsymmetricIntegralConstant_bound hA N (n + q) n' p hp ha.le hap).2
        f hf _ hi' j hj (glyzDyadicSeparated_refine_left hs hu')) (by positivity)
  have hpow := Real.rpow_le_rpow
    (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg ENNReal.toReal_nonneg _) hsum
    (by positivity : 0 ≤ a / 2)
  rw [glyzDyadicBilinearEnergy_refine m N n n' q p ha hB f i j hq] at hpow
  exact (hgain f hf i hi j hj hs).trans
    ((mul_le_mul_of_nonneg_left hpow hD).trans_eq (by ring))

end PlanarNikodym
