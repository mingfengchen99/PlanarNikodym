import PlanarNikodym.Analysis.Fourier.GlyzExactScaleDecoupling
import PlanarNikodym.Analysis.Fourier.GlyzLocalPhaseTransport

/-! Lemma 2.3 for an actual locally smooth cinematic phase. Smooth
extension is performed only away from the compact amplitude support;
the original operator, amplitude, and standard time slices are retained. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal BigOperators ContDiff
namespace PlanarNikodym

/-- The exact-scale Lp decoupling statement (2.20), with arbitrary
power decay in the original L2 input norm. Smoothness is needed only
on an open neighborhood of the compact nondegenerate amplitude support.
The real constant precedes all frequencies and all inputs. -/
theorem Family.lemma_2_3 {d : ℕ} (G : Family 2 d)
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
      ∀ g : Plane → ℂ, MemLp g 2 →
      Function.support g ⊆ {y | y.1 ∈ Icc (-1 : ℝ) 1} →
      Function.support g ⊆ {y | y.2 ∈ Icc rmin rmax} →
      let Φ := fun x : Parameters 2 d × ℝ => G.γ x.2 x.1
      let δ := r ^ (-(1 / (d + 1 : ℝ)))
      lpNorm (glyzRawExtension Φ a g r) p volume ≤
        C * r ^ (coneDecouplingExponent (d + 1) p + ε) *
          (∑ i : Fin (glyzExactTimeCount δ),
            lpNorm (timeSliceExtension Φ a g r (-1 + (i : ℝ) * δ) δ) p volume ^
              (p : ℝ)) ^ (1 / (p : ℝ)) +
        C * r ^ (-Q) * lpNorm g 2 volume := by
  obtain ⟨H, _, _, hH, heqdet, heqext⟩ :=
    G.exists_glyz_global_smooth_phase hK hU hKU hG
  have hdetH : ∀ x ∈ K, H.cinematicDet x ≠ 0 := by
    intro x hx
    rw [heqdet x hx]
    exact hdet x hx
  obtain ⟨C, hC, hmain⟩ := H.exists_glyz_exact_scale_decoupling
    hH ha hc hK hdetH has hKt hp hε hrmin hQ (rmax := rmax)
  refine ⟨C, hC, fun r hr g hg hgt hgr => ?_⟩
  let δ := r ^ (-(1 / (d + 1 : ℝ)))
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
  have h := hmain r hr g hg hgt hgr
  change lpNorm (glyzRawExtension (fun x : Parameters 2 d × ℝ => H.γ x.2 x.1)
      a g r) p volume ≤
    C * r ^ (coneDecouplingExponent (d + 1) p + ε) *
      (∑ i : Fin (glyzExactTimeCount δ),
        lpNorm (timeSliceExtension (fun x : Parameters 2 d × ℝ => H.γ x.2 x.1)
          a g r (-1 + (i : ℝ) * δ) δ) p volume ^ (p : ℝ)) ^ (1 / (p : ℝ)) +
    C * r ^ (-Q) * lpNorm g 2 volume at h
  rw [heqext a has g r, hsum] at h
  exact h

end PlanarNikodym
