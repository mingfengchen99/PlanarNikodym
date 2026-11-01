import PlanarNikodym.Analysis.Fourier.GlyzAffineCutoff

/-! Smooth amplitude truncation inside Schwartz space. This allows actual
operator interpolation without leaving the class on which Fourier support
and critical decoupling have been proved. -/
noncomputable section
open Set Metric
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def glyzAmplitudeBump (a : ℝ) (ha : 0 < a) : ContDiffBump (0 : ℂ) :=
  ⟨a, 2 * a, ha, by linarith⟩

theorem glyzAmplitudeBump_comp_temperate (a : ℝ) (ha : 0 < a)
    (f : SchwartzMap E ℂ) :
    (fun x => glyzAmplitudeBump a ha (f x)).HasTemperateGrowth :=
  ((glyzAmplitudeBump a ha).hasCompactSupport.hasTemperateGrowth
    (glyzAmplitudeBump a ha).contDiff).comp f.hasTemperateGrowth

def glyzSchwartzLow (a : ℝ) (ha : 0 < a) (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x => glyzAmplitudeBump a ha (f x)) f

def glyzSchwartzHigh (a : ℝ) (ha : 0 < a) (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  f - glyzSchwartzLow a ha f

@[simp] theorem glyzSchwartzLow_apply (a : ℝ) (ha : 0 < a)
    (f : SchwartzMap E ℂ) (x : E) :
    glyzSchwartzLow a ha f x = glyzAmplitudeBump a ha (f x) • f x :=
  SchwartzMap.smulLeftCLM_apply_apply (glyzAmplitudeBump_comp_temperate a ha f) f x

@[simp] theorem glyzSchwartzHigh_apply (a : ℝ) (ha : 0 < a)
    (f : SchwartzMap E ℂ) (x : E) :
    glyzSchwartzHigh a ha f x = (1 - glyzAmplitudeBump a ha (f x)) • f x := by
  simp only [glyzSchwartzHigh, sub_apply, glyzSchwartzLow_apply,
    sub_smul, one_smul]

theorem glyzSchwartzLow_add_high (a : ℝ) (ha : 0 < a) (f : SchwartzMap E ℂ) :
    glyzSchwartzLow a ha f + glyzSchwartzHigh a ha f = f := by
  simp [glyzSchwartzHigh]

theorem norm_glyzSchwartzLow_le (a : ℝ) (ha : 0 < a)
    (f : SchwartzMap E ℂ) (x : E) : ‖glyzSchwartzLow a ha f x‖ ≤ 2 * a := by
  rw [glyzSchwartzLow_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (glyzAmplitudeBump a ha).nonneg]
  by_cases hx : ‖f x‖ ≤ 2 * a
  · exact (mul_le_of_le_one_left (norm_nonneg _) (glyzAmplitudeBump a ha).le_one).trans hx
  · have hz : glyzAmplitudeBump a ha (f x) = 0 :=
      (glyzAmplitudeBump a ha).zero_of_le_dist (by
        simpa only [glyzAmplitudeBump, dist_zero_right] using (le_of_not_ge hx))
    rw [hz, zero_mul]
    positivity

theorem norm_glyzSchwartzHigh_le (a : ℝ) (ha : 0 < a)
    (f : SchwartzMap E ℂ) (x : E) : ‖glyzSchwartzHigh a ha f x‖ ≤ ‖f x‖ := by
  rw [glyzSchwartzHigh_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (glyzAmplitudeBump a ha).le_one)]
  apply mul_le_of_le_one_left (norm_nonneg _)
  linarith [(glyzAmplitudeBump a ha).nonneg (x := f x)]

theorem glyzSchwartzHigh_eq_zero (a : ℝ) (ha : 0 < a)
    (f : SchwartzMap E ℂ) {x : E} (hx : ‖f x‖ ≤ a) :
    glyzSchwartzHigh a ha f x = 0 := by
  have hb : glyzAmplitudeBump a ha (f x) = 1 :=
    (glyzAmplitudeBump a ha).one_of_mem_closedBall (by
      simpa only [mem_closedBall, dist_zero_right, glyzAmplitudeBump] using hx)
  simp only [glyzSchwartzHigh_apply, hb, sub_self, zero_smul]

end PlanarNikodym
