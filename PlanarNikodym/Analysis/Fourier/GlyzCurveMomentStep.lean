import PlanarNikodym.Analysis.Fourier.GlyzCurveDyadicStep
import PlanarNikodym.Analysis.Fourier.GlyzEnlargedMomentDecoupling

/-! A genuine projected-curve refinement estimate from the actual
lower-dimensional moment decoupling constants. The radius enlargement,
affine rescaling, Taylor comparison, and intermediate supports are all
proved; no curve decoupling estimate is an assumption. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform BigOperators NNReal ENNReal
namespace PlanarNikodym

/-- One actual dyadic refinement of a projected curve, with the
lower-dimensional moment loss as the only analytic induction premise. -/
theorem exists_uniform_glyz_curve_step_of_admissible_square_loss
    (l r : ℕ) {ν Q : ℝ} (hν : 0 < ν) (hQ : 0 < Q)
    {p : ℝ≥0} (hp : 1 ≤ p) {α : ℝ} (hα : GlyzAdmissibleSquareLoss l p α) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 1 ≤ C ∧
      ∀ (t : ℝ) (N n m i : ℕ), n ≤ m → m ≤ N → i < 2 ^ n →
      glyzDyadicScale n < ρ →
      glyzDyadicScale m ≤ glyzDyadicScale n →
      glyzDyadicScale n ^ (l + 1) ≤ glyzDyadicScale m ^ l →
      (glyzDyadicScale n * i, t) ∈ separatedMixedCenters ν →
      (∀ j < 2 ^ (m - n),
        (glyzDyadicCenter m (i * 2 ^ (m - n) + j), t) ∈ separatedMixedCenters ν) →
      ∀ f : ℕ → SchwartzMap (GlyzSpace l) ℂ,
      (∀ j < 2 ^ N, Function.support (𝓕 (f j : GlyzSpace l → ℂ)) ⊆
        glyzEnlargedCurveBox (glyzCoordinateCurve l r t) l
          (glyzDyadicCenter N j) (glyzDyadicScale N) Q) →
      lpNorm ((glyzDyadicBlock f N n i : SchwartzMap (GlyzSpace l) ℂ) :
        GlyzSpace l → ℂ) p volume ^ 2 ≤
        (C * (2 : ℝ) ^ (α * (m - n : ℕ))) * glyzDyadicBlock
          (fun j => lpNorm ((glyzDyadicBlock f N m j : SchwartzMap (GlyzSpace l) ℂ) :
            GlyzSpace l → ℂ) p volume ^ 2) m n i := by
  obtain ⟨ρ, R, hρ, hρ1, hR, hstep⟩ :=
    exists_uniform_glyzCoordinateCurve_dyadic_step l r hν hQ
  obtain ⟨C, hC, hmoment⟩ :=
    glyz_enlarged_affine_dyadic_decoupling_of_admissible_square_loss hp hα R
  refine ⟨ρ, max C 1, hρ, hρ1, le_max_right _ _,
    fun t N n m i hnm hmN hi hshort hδκ hscale hsep hchildren f hf => ?_⟩
  let a : ℝ := glyzDyadicScale n * i
  let b : ℝ := glyzDyadicScale n * (i + 1)
  have hκ := glyzDyadicScale_pos n
  have hlength : b - a = glyzDyadicScale n := by dsimp [a, b]; ring
  have hbound : b ≤ 1 := by
    have hi' : (i : ℝ) + 1 ≤ (2 : ℝ) ^ n := by exact_mod_cast hi
    have hh := mul_le_mul_of_nonneg_left hi' hκ.le
    have heq : glyzDyadicScale n * (2 : ℝ) ^ n = 1 := inv_mul_cancel₀ (by positivity)
    simpa only [heq] using hh
  have ha : a ∈ Icc (-1 : ℝ) 1 := by
    have ha0 : 0 ≤ a := by dsimp [a]; positivity
    constructor
    · linarith
    · linarith
  have hb : b ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · have hb0 : 0 ≤ b := by dsimp [b]; positivity
      linarith
    · exact hbound
  have he : n + (m - n) = m := Nat.add_sub_of_le hnm
  have hc (j : ℕ) :
      glyzDyadicCenter m (i * 2 ^ (m - n) + j) - a =
        0 + glyzDyadicScale n * glyzDyadicCenter (m - n) j := by
    have hcenter := glyzDyadicCenter_rescale n (m - n) i j
    rw [he] at hcenter
    rw [← hcenter]
    dsimp [a]
    ring
  have hs : glyzDyadicScale m = glyzDyadicScale n * glyzDyadicScale (m - n) := by
    rw [← glyzDyadicScale_add, he]
  apply hstep t a b ha hb (by linarith) (by simpa only [hlength] using hshort) hsep
    N n m i hnm hmN hi (by simpa only [hlength] using hδκ)
    (by simpa only [hlength] using hscale) f p (max C 1 * (2 : ℝ) ^ (α * (m - n : ℕ)))
  · intro j hj
    refine ⟨?_, hchildren j hj⟩
    have hjc := glyzDyadicCenter_mem_Icc hj
    have hid := hc j
    constructor <;> nlinarith [mul_nonneg hκ.le hjc.1,
      mul_le_mul_of_nonneg_left hjc.2 hκ.le]
  · exact hf
  · intro g hg
    have h := hmoment (m - n) 0 (glyzDyadicScale n) hκ g (by
      intro j hj
      have hsupport := hg j (Finset.mem_range.mp hj)
      simpa only [hc j, hs] using hsupport)
    have hcoef : C * (2 : ℝ) ^ (α * (m - n : ℕ)) ≤
        max C 1 * (2 : ℝ) ^ (α * (m - n : ℕ)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    have henergy := glyzDyadicSquareEnergy_nonneg l (m - n) p g
    have ht := h.trans (mul_le_mul_of_nonneg_right hcoef henergy)
    have hfun : ((∑ j ∈ Finset.range (2 ^ (m - n)), g j :
        SchwartzMap (GlyzSpace l) ℂ) : GlyzSpace l → ℂ) =
        fun x => ∑ j ∈ Finset.range (2 ^ (m - n)), g j x := by
      ext x
      simp only [sum_apply]
    rw [hfun]
    exact ht

end PlanarNikodym
