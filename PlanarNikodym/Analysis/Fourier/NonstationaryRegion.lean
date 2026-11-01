import PlanarNikodym.Analysis.Fourier.BandOscillatoryRepresentation

/-! The actual normalized band lies away from zero, and sufficiently
horizontal frequencies have a uniformly nonstationary time phase on the
compact cutoff support. -/
noncomputable section
open Set
open scoped ContDiff

namespace PlanarNikodym

theorem FrequencyCutoff.bandSymbol_tsupport_norm_ge_scale (L : FrequencyCutoff)
    (k : ℕ) {ξ : Plane} (hξ : ξ ∈ tsupport (L.bandSymbol k)) : (2 : ℝ) ^ k ≤ ‖ξ‖ := by
  apply closure_minimal (s := Function.support (L.bandSymbol k)) _
    (isClosed_le continuous_const continuous_norm) hξ
  intro η hη
  exact le_of_lt (lt_of_not_ge (fun h => hη (L.bandSymbol_vanishes_below_scale k h)))

def Family.graphPhase {d : ℕ} (G : Family 2 d) (q : Parameters 2 d)
    (ξ : Plane) (t : ℝ) : ℝ := fourierPhase (G.graphMap q t) ξ

theorem Family.graphPhase_hasDerivAt {d : ℕ} (G : Family 2 d)
    {q : Parameters 2 d} {t : ℝ}
    (hγ : ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) (t, q))
    (ξ : Plane) :
    HasDerivAt (G.graphPhase q ξ)
      (ξ.1 + timeDerivative (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) 1 (t, q) * ξ.2) t := by
  have hfull := (hγ.differentiableAt (by simp)).hasFDerivAt
  have hcomp := hfull.comp_hasDerivAt (f := fun s : ℝ => (s, q)) t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t q))
  have hslice : HasDerivAt (fun s : ℝ => G.γ s q)
      (timeDerivative (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) 1 (t, q)) t :=
    hcomp
  change HasDerivAt (fun s : ℝ => s * ξ.1 + G.γ s q * ξ.2) _ t
  convert ((hasDerivAt_id t).mul_const ξ.1).add (hslice.mul_const ξ.2) using 1 <;> first
    | rfl
    | simp only [one_mul]

/-- The nonstationarity width is chosen from an actual compact-support
bound for the time slope. It is independent of the point and frequency. -/
theorem Family.exists_uniform_nonstationary_region {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ ∀ x ∈ tsupport χ, ∀ ξ : Plane,
      1 ≤ ‖ξ‖ → |ξ.2| ≤ δ → 1 / 2 ≤ |deriv (G.graphPhase x.2 ξ) x.1| := by
  let S : ℝ × Parameters 2 d → ℝ :=
    timeDerivative (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) 1
  have hS : ContinuousOn S (tsupport χ) := by
    intro x hx
    exact (((hγ x hx).continuousAt_fderiv (by simp)).clm_apply continuousAt_const).continuousWithinAt
  obtain ⟨B, hB⟩ := hc.isCompact.exists_bound_of_continuousOn hS
  let M : ℝ := |B|
  have hM : 0 ≤ M := abs_nonneg B
  have hbound : ∀ x ∈ tsupport χ, |S x| ≤ M := by
    intro x hx
    exact (le_of_eq (Real.norm_eq_abs _).symm).trans ((hB x hx).trans (le_abs_self B))
  let δ : ℝ := 1 / (4 * (M + 1))
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδeq : δ * (M + 1) = 1 / 4 := by dsimp [δ]; field_simp
  have hδle : δ ≤ 1 / 4 := by nlinarith [mul_nonneg hM hδpos.le]
  refine ⟨δ, hδpos, hδle, ?_⟩
  intro x hx ξ hξ hξ₂
  have hξ₁ : 1 ≤ |ξ.1| := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs] at hξ
    rcases le_max_iff.mp hξ with h | h
    · exact h
    · linarith
  have hsmall : |S x * ξ.2| ≤ 1 / 4 := by
    rw [abs_mul]
    have hp := mul_le_mul (hbound x hx) hξ₂ (abs_nonneg ξ.2) hM
    nlinarith
  have htri : |ξ.1| ≤ |ξ.1 + S x * ξ.2| + |S x * ξ.2| := by
    calc
      |ξ.1| = |(ξ.1 + S x * ξ.2) - S x * ξ.2| := by congr 1; ring
      _ ≤ _ := by simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (ξ.1 + S x * ξ.2) (-(S x * ξ.2))
  rw [(G.graphPhase_hasDerivAt (hγ x hx) ξ).deriv]
  change 1 / 2 ≤ |ξ.1 + S x * ξ.2|
  linarith

end PlanarNikodym
