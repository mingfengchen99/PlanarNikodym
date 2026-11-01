import PlanarNikodym.Analysis.Fourier.GlyzBilinearAssembly

/-! Uniform summation of scale-dependent bilinear bounds. This proves
the analytic transfer of a geometric scale gain, without assuming that
the deeper bilinear gain has already been established. -/
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace PlanarNikodym

theorem glyz_reverse_geom_sum {ρ : ℝ} (hρ : 1 < ρ) (N : ℕ) :
    (∑ n ∈ Finset.range N, ρ ^ (N - n)) = ρ * (ρ ^ N - 1) / (ρ - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have he : (∑ n ∈ Finset.range N, ρ ^ (N + 1 - n)) =
        ρ * ∑ n ∈ Finset.range N, ρ ^ (N - n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [show N + 1 - n = (N - n) + 1 by have := Finset.mem_range.mp hn; omega, pow_succ]
      ring
    rw [he, ih]
    simp only [Nat.add_sub_cancel_left, pow_succ]
    field_simp [sub_ne_zero.mpr hρ.ne']
    ring

theorem glyz_reverse_geom_sum_le {ρ : ℝ} (hρ : 1 < ρ) (N : ℕ) :
    (∑ n ∈ Finset.range N, ρ ^ (N - n)) ≤ ρ / (ρ - 1) * ρ ^ N := by
  rw [glyz_reverse_geom_sum hρ]
  have hd : 0 < ρ - 1 := by linarith
  apply (div_le_iff₀ hd).2
  field_simp
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A geometric bound on the actual bilinear terms transfers to a
linear bound with a constant independent of the dyadic depth N. -/
theorem glyz_bilinear_to_linear_geometric (f : ℕ → SchwartzMap E ℂ) (N : ℕ)
    (p : ℝ≥0) (hp : 2 ≤ p) {K ρ : ℝ} (hK : 0 ≤ K) (hρ : 1 < ρ)
    (hbil : ∀ n < N, ∀ i < 2 ^ (n + 1), ∀ j < 2 ^ (n + 1),
      2 ≤ Nat.dist i j ∧ Nat.dist (i / 2) (j / 2) ≤ 1 →
      glyzBilinearLp p (glyzDyadicBlock f N (n + 1) i) (glyzDyadicBlock f N (n + 1) j) ≤
        (K * ρ ^ (N - n)) *
          (glyzDyadicBlock (fun k => lpNorm (f k : E → ℂ) p volume ^ (2 : ℕ)) N (n + 1) i +
            glyzDyadicBlock (fun k => lpNorm (f k : E → ℂ) p volume ^ (2 : ℕ)) N (n + 1) j)) :
    lpNorm (fun x => ∑ i ∈ Finset.range (2 ^ N), f i x) p volume ^ (2 : ℕ) ≤
      ((6 + 8 * K * (ρ / (ρ - 1))) * ρ ^ N) *
        ∑ k ∈ Finset.range (2 ^ N), lpNorm (f k : E → ℂ) p volume ^ (2 : ℕ) := by
  have hρ0 : 0 ≤ ρ := le_trans zero_le_one hρ.le
  have hb := glyz_bilinear_to_linear f N p hp (fun n => K * ρ ^ (N - n))
    (fun _ _ => mul_nonneg hK (pow_nonneg hρ0 _)) hbil
  have hs := mul_le_mul_of_nonneg_left (glyz_reverse_geom_sum_le hρ N) hK
  have hc : 6 + 8 * ∑ n ∈ Finset.range N, K * ρ ^ (N - n) ≤
      (6 + 8 * K * (ρ / (ρ - 1))) * ρ ^ N := by
    rw [← Finset.mul_sum]
    nlinarith [one_le_pow₀ hρ.le (n := N)]
  exact hb.trans (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg fun k _ => sq_nonneg _))

end PlanarNikodym
