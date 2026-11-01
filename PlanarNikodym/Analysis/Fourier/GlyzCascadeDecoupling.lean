import PlanarNikodym.Analysis.Fourier.GlyzCascadeExactScaleDecoupling
import PlanarNikodym.Analysis.Fourier.GlyzLocalPhaseTransport

/-! Equation (2.30) for an actual locally smooth cinematic phase. Smooth
extension is performed only away from the compact amplitude support;
the original operator, amplitude, and standard time slices are retained. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal BigOperators ContDiff
namespace PlanarNikodym

/-- Successive degree decoupling (2.30), with arbitrary
power decay in the original L1 input mass. Smoothness is needed only
on an open neighborhood of the compact nondegenerate amplitude support.
The real constant precedes all frequencies and all inputs. -/
theorem Family.glyz_cascade_decoupling {d : ℕ} (G : Family 2 d)
    (hd : 1 ≤ d)
    {K U : Set (ℝ × Parameters 2 d)} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hG : ∀ x ∈ U, ContDiffAt ℝ ∞
      (fun z : ℝ × Parameters 2 d => G.γ z.1 z.2) x)
    {a : Parameters 2 d × Plane → ℂ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hdet : ∀ x ∈ K, G.cinematicDet x ≠ 0)
    (has : ∀ x t η, a (x, t, η) ≠ 0 → (t, x) ∈ K)
    (hKt : ∀ x ∈ K, x.1 ∈ Ioo (-1 : ℝ) 1)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent (d + 1) ≤ p)
    {ε rmin rmax Q : ℝ} (hε : 0 < ε) (hrmin : 0 < rmin) (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      ∀ g : Plane → ℂ, Integrable g →
      Function.support g ⊆ {y | y.2 ∈ Icc rmin rmax} →
      let Φ := fun x : Parameters 2 d × ℝ => G.γ x.2 x.1
      let δ := r ^ (-(1 / (2 : ℝ)))
      lpNorm (glyzRawExtension Φ a g r) p volume ≤
        C * r ^ ((1 / 2 - (d + 1 : ℝ) / p) + ε) *
          (∑ i : Fin (glyzExactTimeCount δ),
            lpNorm (timeSliceExtension Φ a g r (-1 + (i : ℝ) * δ) δ) p volume ^
              (p : ℝ)) ^ (1 / (p : ℝ)) +
        C * r ^ (-Q) * (∫ y, ‖g y‖) := by
  obtain ⟨H, _, _, hH, heqdet, heqext⟩ :=
    G.exists_glyz_global_smooth_phase hK hU hKU hG
  have hdetH : ∀ x ∈ K, H.cinematicDet x ≠ 0 := by
    intro x hx
    rw [heqdet x hx]
    exact hdet x hx
  obtain ⟨C, hC, hmain⟩ := H.exists_glyz_cascade_exact_scale_decoupling_L1 hd
    hH ha hc hK hdetH has hKt hp hε hrmin hQ (rmax := rmax)
  refine ⟨C, hC, fun r hr g hg hgr => ?_⟩
  let δ := r ^ (-(1 / (2 : ℝ)))
  have hδ : 0 < δ := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hr) _
  have hpieces (i : Fin (glyzExactTimeCount δ)) :
      timeSliceExtension (fun x : Parameters 2 d × ℝ => H.γ x.2 x.1)
        a g r (-1 + (i : ℝ) * δ) δ =
      timeSliceExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1)
        a g r (-1 + (i : ℝ) * δ) δ := by
    rw [← glyzRawExtension_exactTimePiece_eq_timeSliceExtension _ a g r hδ i,
      ← glyzRawExtension_exactTimePiece_eq_timeSliceExtension _ a g r hδ i]
    exact heqext a has (glyzExactTimePiece δ i g) r
  have hsum :
      (∑ i : Fin (glyzExactTimeCount δ),
        lpNorm (timeSliceExtension (fun x : Parameters 2 d × ℝ => H.γ x.2 x.1)
          a g r (-1 + (i : ℝ) * δ) δ) p volume ^ (p : ℝ)) =
      ∑ i : Fin (glyzExactTimeCount δ),
        lpNorm (timeSliceExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1)
          a g r (-1 + (i : ℝ) * δ) δ) p volume ^ (p : ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hpieces i]
  have h := hmain r hr g hg hgr
  change lpNorm (glyzRawExtension (fun x : Parameters 2 d × ℝ => H.γ x.2 x.1)
      a g r) p volume ≤
    C * r ^ ((1 / 2 - (d + 1 : ℝ) / p) + ε) *
      (∑ i : Fin (glyzExactTimeCount δ),
        lpNorm (timeSliceExtension (fun x : Parameters 2 d × ℝ => H.γ x.2 x.1)
          a g r (-1 + (i : ℝ) * δ) δ) p volume ^ (p : ℝ)) ^ (1 / (p : ℝ)) +
    C * r ^ (-Q) * (∫ y, ‖g y‖) at h
  rw [heqext a has g r, hsum] at h
  exact h

end PlanarNikodym
