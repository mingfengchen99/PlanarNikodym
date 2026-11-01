import PlanarNikodym.Analysis.Fourier.GlyzDyadicIntervalGeometry
import PlanarNikodym.Analysis.Fourier.CompactKernelIntegration

/-! Actual disjoint dyadic restrictions of the input data. The half-open
intervals preserve exact reconstruction and exact L1 mass addition. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal ContDiff
namespace PlanarNikodym

/-- A finite arithmetic subdivision acts exactly on any input function. -/
theorem glyz_arithmetic_indicator_sum {Y V : Type*} [AddCommMonoid V]
    (t : Y → ℝ) (g : Y → V) (a δ : ℝ) (hδ : 0 ≤ δ) (M : ℕ) :
    (∑ j ∈ Finset.range M, ({y | t y ∈ Ico (a + δ * j) (a + δ * ((j : ℝ) + 1))}).indicator g) =
      ({y | t y ∈ Ico a (a + δ * M)}).indicator g := by
  classical
  induction M with
  | zero => ext y; simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    have hab : a ≤ a + δ * M := le_add_of_nonneg_right (mul_nonneg hδ (Nat.cast_nonneg M))
    have hbc : a + δ * M ≤ a + δ * ((M : ℝ) + 1) := by nlinarith
    have hu : {y | t y ∈ Ico a (a + δ * ((M : ℝ) + 1))} =
        {y | t y ∈ Ico a (a + δ * M)} ∪
          {y | t y ∈ Ico (a + δ * M) (a + δ * ((M : ℝ) + 1))} := by
      ext y
      exact Set.ext_iff.mp (Set.Ico_union_Ico_eq_Ico hab hbc).symm (t y)
    have hd : Disjoint {y | t y ∈ Ico a (a + δ * M)}
        {y | t y ∈ Ico (a + δ * M) (a + δ * ((M : ℝ) + 1))} :=
      Set.disjoint_left.mpr fun y hy hy' => hy.2.not_ge hy'.1
    push_cast
    rw [hu, Set.indicator_union_of_disjoint hd]
    rfl

def glyzDyadicInputSet (n i : ℕ) : Set Plane :=
  {y | y.1 ∈ Ico (glyzDyadicLeft n i) (glyzDyadicRight n i)}

def glyzDyadicInput {V : Type*} [Zero V] (n i : ℕ) (g : Plane → V) : Plane → V :=
  (glyzDyadicInputSet n i).indicator g

theorem measurableSet_glyzDyadicInputSet (n i : ℕ) : MeasurableSet (glyzDyadicInputSet n i) :=
  measurableSet_Ico.preimage measurable_fst

theorem integrable_glyzDyadicInput {g : Plane → ℂ} (hg : Integrable g) (n i : ℕ) :
    Integrable (glyzDyadicInput n i g) := hg.indicator (measurableSet_glyzDyadicInputSet n i)

theorem glyzDyadicInput_refine {V : Type*} [AddCommMonoid V]
    (g : Plane → V) (n q i : ℕ) :
    glyzDyadicInput n i g = ∑ j ∈ Finset.range (2 ^ q), glyzDyadicInput (n + q) (i * 2 ^ q + j) g := by
  have hscale : glyzDyadicScale (n + q) * (2 : ℝ) ^ q = glyzDyadicScale n := by
    rw [glyzDyadicScale_add, mul_assoc]
    have hq : glyzDyadicScale q * (2 : ℝ) ^ q = 1 := inv_mul_cancel₀ (by positivity)
    rw [hq, mul_one]
  have hleft (j : ℕ) : glyzDyadicLeft (n + q) (i * 2 ^ q + j) =
      glyzDyadicLeft n i + glyzDyadicScale (n + q) * j := by
    unfold glyzDyadicLeft
    push_cast
    nlinarith
  have hright (j : ℕ) : glyzDyadicRight (n + q) (i * 2 ^ q + j) =
      glyzDyadicLeft n i + glyzDyadicScale (n + q) * ((j : ℝ) + 1) := by
    unfold glyzDyadicRight glyzDyadicLeft
    push_cast
    nlinarith
  have hend : glyzDyadicLeft n i + glyzDyadicScale (n + q) * ((2 ^ q : ℕ) : ℝ) =
      glyzDyadicRight n i := by
    push_cast
    rw [hscale]
    unfold glyzDyadicLeft glyzDyadicRight
    ring
  unfold glyzDyadicInput glyzDyadicInputSet
  simp_rw [hleft, hright]
  rw [glyz_arithmetic_indicator_sum Prod.fst g _ _ (glyzDyadicScale_pos (n + q)).le,
    hend]

theorem glyzDyadicInput_zero_of_supported {V : Type*} [Zero V] (g : Plane → V)
    (hs : Function.support g ⊆ {y | y.1 ∈ Ico (0 : ℝ) 1}) : glyzDyadicInput 0 0 g = g := by
  have hset : glyzDyadicInputSet 0 0 = {y : Plane | y.1 ∈ Ico (0 : ℝ) 1} := by
    simp [glyzDyadicInputSet, glyzDyadicLeft, glyzDyadicRight, glyzDyadicScale]
  unfold glyzDyadicInput
  rw [hset]
  exact Set.indicator_eq_self.mpr hs

@[simp] theorem enorm_glyzDyadicInput (g : Plane → ℂ) (n i : ℕ) (y : Plane) :
    ‖glyzDyadicInput n i g y‖ₑ = glyzDyadicInput n i (fun z => ‖g z‖ₑ) y := by
  by_cases hy : y ∈ glyzDyadicInputSet n i
  · simp [glyzDyadicInput, hy]
  · simp [glyzDyadicInput, hy]

/-- Exact L1 mass conservation for every parent and all its descendants. -/
theorem glyzDyadicInput_lintegral_enorm_refine {g : Plane → ℂ} (hg : Integrable g)
    (n q i : ℕ) :
    (∫⁻ y, ‖glyzDyadicInput n i g y‖ₑ) =
      ∑ j ∈ Finset.range (2 ^ q), (∫⁻ y, ‖glyzDyadicInput (n + q) (i * 2 ^ q + j) g y‖ₑ) := by
  simp only [enorm_glyzDyadicInput]
  rw [glyzDyadicInput_refine]
  simp only [Finset.sum_apply]
  apply lintegral_finsetSum'
  intro j hj
  simpa only [enorm_glyzDyadicInput] using
    (integrable_glyzDyadicInput hg (n + q) (i * 2 ^ q + j)).aestronglyMeasurable.enorm

theorem glyzDyadicInput_lintegral_enorm_sum {g : Plane → ℂ} (hg : Integrable g)
    (hs : Function.support g ⊆ {y | y.1 ∈ Ico (0 : ℝ) 1}) (n : ℕ) :
    (∑ i ∈ Finset.range (2 ^ n), ∫⁻ y, ‖glyzDyadicInput n i g y‖ₑ) = ∫⁻ y, ‖g y‖ₑ := by
  have h := glyzDyadicInput_lintegral_enorm_refine hg 0 n 0
  simpa only [zero_add, zero_mul, glyzDyadicInput_zero_of_supported g hs] using h.symm

/-- The actual compact smooth integral operator respects the dyadic
parent decomposition. Integrability is derived from the original L1
data and the compact smooth kernel. -/
theorem glyz_compactKernel_dyadicInput_refine {X : Type}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {g : Plane → ℂ} (hg : Integrable g) {H : X × Plane → ℂ}
    (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H) (n q i : ℕ) (x : X) :
    (∫ y, glyzDyadicInput n i g y * H (x, y)) =
      ∑ j ∈ Finset.range (2 ^ q), ∫ y, glyzDyadicInput (n + q) (i * 2 ^ q + j) g y * H (x, y) := by
  rw [glyzDyadicInput_refine]
  simp only [Finset.sum_apply, Finset.sum_mul]
  apply integral_finsetSum
  intro j hj
  exact integrable_compactKernel_smul volume (integrable_glyzDyadicInput hg _ _) hH hc x

end PlanarNikodym
