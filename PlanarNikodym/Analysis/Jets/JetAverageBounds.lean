import PlanarNikodym.Analysis.Jets.JetAmplitudeBounds

/-! Actual time-integrated majorants for auxiliary average jets. The
majorant is restricted to the true cutoff support, so no regularity of
the geometric extension outside that support is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace PlanarNikodym

def cutoffTimeSection {d : ℕ} (χ : Cutoff d) (q : Parameters 2 d) : Set ℝ :=
  (fun t => (t, q)) ⁻¹' tsupport χ

theorem isCompact_cutoffTimeSection {d : ℕ} (χ : Cutoff d)
    (hc : HasCompactSupport χ) (q : Parameters 2 d) : IsCompact (cutoffTimeSection χ q) := by
  apply (hc.isCompact.image continuous_fst).of_isClosed_subset
    ((isClosed_tsupport χ).preimage (continuous_id.prodMk continuous_const))
  intro t ht
  exact ⟨(t, q), ht, rfl⟩

def Family.timeInputJetMajorant {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (f : Plane → ℂ) (j : ℕ) (q : Parameters 2 d) (t : ℝ) : ℝ :=
  (cutoffTimeSection χ q).indicator
    (fun t => ∑ m ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ m f (G.graphMap q t)‖) t

theorem Family.timeInputJetMajorant_nonneg {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (f : Plane → ℂ) (j : ℕ) (q : Parameters 2 d) (t : ℝ) :
    0 ≤ G.timeInputJetMajorant χ f j q t :=
  indicator_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) _

theorem Family.timeInputJetMajorant_integrable {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (j : ℕ) (q : Parameters 2 d) :
    Integrable (G.timeInputJetMajorant χ f j q) := by
  have hK := isCompact_cutoffTimeSection χ hc q
  have hgraph : ContinuousOn (G.graphMap q) (cutoffTimeSection χ q) := by
    intro t ht
    exact (continuousAt_id.prodMk ((hγ (t, q) ht).continuousAt.comp (f := fun t : ℝ => (t, q))
      (continuousAt_id.prodMk continuousAt_const))).continuousWithinAt
  have hsum : ContinuousOn (fun t : ℝ =>
      ∑ m ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ m f (G.graphMap q t)‖)
      (cutoffTimeSection χ q) := by
    apply continuousOn_finsetSum
    intro m _
    exact ((contDiff_infty.mp hf m).continuous_iteratedFDeriv'.norm).comp_continuousOn hgraph
  exact (hsum.integrableOn_compact hK).integrable_indicator hK.measurableSet

/-- The finite amplitude bound integrated over time gives an actual
auxiliary-jet bound. The same constant works for every smooth input. -/
theorem Family.exists_uniform_auxiliary_cutoffJet_norm_bound {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Plane → ℂ), ContDiff ℝ ∞ f → ∀ q : Parameters 2 d,
      ‖iteratedFDeriv ℝ j (fun u => G.cutoffAverage χ f (q.1, u)) q.2‖ ≤
        C * ∫ t : ℝ, G.timeInputJetMajorant χ f j q t := by
  obtain ⟨C, hC, hAmp⟩ := G.exists_uniform_cutoffJetAmplitude_bound χ hχ hc hγ j
  refine ⟨C, hC, ?_⟩
  intro f hf q
  have hpoint (t : ℝ) : ‖G.cutoffJetAmplitude χ f j q.1 t q.2‖ ≤
      C * G.timeInputJetMajorant χ f j q t := by
    by_cases ht : t ∈ cutoffTimeSection χ q
    · simpa only [Family.timeInputJetMajorant, indicator_of_mem ht]
        using hAmp f hf q.1 t q.2
    · have hx : (t, (q.1, q.2)) ∉ tsupport χ := ht
      simp only [Family.cutoffJetAmplitude, if_neg hx, norm_zero,
        Family.timeInputJetMajorant, indicator_of_notMem ht, mul_zero, le_refl]
  rw [G.auxiliary_cutoffJet_eq_integral_amplitude χ hχ hc hγ hf j q.1 q.2]
  calc
    _ ≤ ∫ t : ℝ, ‖G.cutoffJetAmplitude χ f j q.1 t q.2‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, C * G.timeInputJetMajorant χ f j q t := integral_mono
      (G.cutoffJetAmplitude_integrable χ hχ hc hγ hf j q.1 q.2).norm
      ((G.timeInputJetMajorant_integrable χ hc hγ hf j q).const_mul C) hpoint
    _ = _ := integral_const_mul _ _

end PlanarNikodym
