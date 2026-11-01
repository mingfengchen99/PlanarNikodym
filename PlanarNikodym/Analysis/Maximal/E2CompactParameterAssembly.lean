import PlanarNikodym.Analysis.Maximal.E2IntervalMaximal
import PlanarNikodym.Analysis.Maximal.E2CompactCutoff
import PlanarNikodym.Analysis.Maximal.E2LocalSmoothExponentRange

/-! Quantitative assembly on the original compact parameter domain.
One constructed cutoff covers the entire closed time interval × compact
parameter set; the original operator is Definition 1.3 itself. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff
namespace PlanarNikodym

theorem Family.intervalMaximal_e2_le_cutoff_norm {d : ℕ} (G : Family 2 d)
    (K : Set (Parameters 2 d)) (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ t ∈ G.I.carrier, ∀ q ∈ K, 1 ≤ χ (t, q))
    {f : Plane → ℂ} (hf : Continuous f) (z : Base 2) :
    G.intervalMaximal_e2 K f z ≤ G.cutoffMaximal χ (fun x => (‖f x‖ : ℂ)) z := by
  apply le_trans _ (G.positiveMaximal_le_cutoffMaximal K hχ hc hγ hχ0 hχ1 hf.norm
    (fun _ => norm_nonneg _) z)
  apply iSup_le
  intro u
  apply iSup_le
  intro hu
  apply le_trans _ (G.positiveAverage_le_maximal (fun x => ENNReal.ofReal ‖f x‖) hu)
  have hh := enorm_integral_le_lintegral_enorm (fun t => f (G.graphMap (z, u) t))
    (μ := volume.restrict G.I.carrier)
  simpa only [Family.intervalAverage_e2, Family.positiveAverage, ofReal_norm] using hh

theorem Family.intervalMaximal_e2_bound_of_cutoff {d : ℕ} (G : Family 2 d)
    (hG : G.IsSmooth) (K : Set (Parameters 2 d)) (hK : IsCompact K) (hKW : K ⊆ G.W)
    (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ t ∈ G.I.carrier, ∀ q ∈ K, 1 ≤ χ (t, q))
    (p : ℝ≥0∞) (C : ℝ≥0)
    (hbound : ∀ f : Plane → ℂ, Continuous f → HasCompactSupport f → MemLp f p volume →
      eLpNorm (G.cutoffMaximal χ f) p volume ≤ C * eLpNorm f p volume)
    {f : Plane → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (hfp : MemLp f p volume) :
    Measurable (G.intervalMaximal_e2 K f) ∧
      eLpNorm (G.intervalMaximal_e2 K f) p volume ≤ C * eLpNorm f p volume := by
  obtain ⟨x₀, hx₀⟩ := hf.norm.exists_forall_ge_of_hasCompactSupport hfc.norm
  refine ⟨G.measurable_intervalMaximal_e2 hG K hK hKW hf hx₀, ?_⟩
  let g : Plane → ℂ := fun x => (‖f x‖ : ℂ)
  have hg : Continuous g := Complex.continuous_ofReal.comp hf.norm
  have hgc : HasCompactSupport g := hfc.norm.comp_left (g := Complex.ofRealCLM) rfl
  have hnorm (x : Plane) : ‖g x‖ = ‖f x‖ := by
    simp only [g, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  have hgp : MemLp g p volume := hfp.congr_norm hg.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => (hnorm x).symm))
  calc
    _ ≤ eLpNorm (G.cutoffMaximal χ g) p volume :=
      eLpNorm_mono_enorm (fun z => by
        simpa only [enorm_eq_self] using
          G.intervalMaximal_e2_le_cutoff_norm K χ hχ hc hγ hχ0 hχ1 hf z)
    _ ≤ C * eLpNorm g p volume := hbound g hg hgc hgp
    _ = _ := by rw [eLpNorm_congr_norm_ae (Filter.Eventually.of_forall hnorm)]

theorem Family.compact_intervalMaximal_e2_bound_of_geometric_endpoint {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) (hdim : 1 ≤ d)
    (K : Set (Parameters 2 d)) (hK : IsCompact K) (hKW : K ⊆ G.W)
    (hd : ∀ t ∈ G.I.carrier, ∀ q ∈ K, G.cinematicDet (t, q) ≠ 0)
    (L : FrequencyCutoff)
    (hgeometric : ∀ χ : Cutoff d, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      (∀ x, 0 ≤ χ x) → (∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0) →
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0, ∀ k : ℕ, ∀ f : Plane → ℂ,
      Integrable f → MemLp f (d + 2 : ℝ≥0) volume →
      eLpNorm (G.cutoffMaximal χ (L.band k f)) (d + 2 : ℝ≥0) volume ≤
        C * dyadicWeight ε k * eLpNorm f (d + 2 : ℝ≥0) volume)
    (p : ℝ≥0) (hp : (d + 2 : ℝ≥0) < p) :
    ∃ C : ℝ≥0, ∀ f : Plane → ℂ, Continuous f → HasCompactSupport f → MemLp f p volume →
      Measurable (G.intervalMaximal_e2 K f) ∧
        eLpNorm (G.intervalMaximal_e2 K f) p volume ≤ C * eLpNorm f p volume := by
  obtain ⟨χ, hχ, hc, hr, hχ1, hdet⟩ := G.exists_compact_interval_cutoff_e2 hG K hK hd
  obtain ⟨η, hη, CH, hCH⟩ := G.smooth_summable_dyadic_estimate_of_geometric_endpoint_e2
    hG hdim χ hχ hc (fun x => (hr x).1) hdet L
    (hgeometric χ hχ hc (fun x => (hr x).1) hdet) p hp
  obtain ⟨C, hC⟩ := G.cutoffMaximal_continuous_tests_of_summable_dyadic_e2 χ hχ.continuous hc
    (fun _ _ => hG.continuous.continuousAt) L p (by linarith [NNReal.coe_nonneg (d : ℝ≥0)]) hη CH hCH
  refine ⟨C, fun f hf hfc hfp => ?_⟩
  apply G.intervalMaximal_e2_bound_of_cutoff hG.contDiffOn K hK hKW χ hχ.continuous hc
    (fun _ _ => hG.continuous.continuousAt) (fun x => (hr x).1)
    (fun t ht q hq => (hχ1 t ht q hq).symm.le) p C
    (fun f hf hfc hfp => ?_) hf hfc hfp
  obtain ⟨x₀, hx₀⟩ := hf.norm.exists_forall_ge_of_hasCompactSupport hfc.norm
  exact (hC f hf (hf.integrable_of_hasCompactSupport hfc) hfp ⟨‖f x₀‖, hx₀⟩).2

end PlanarNikodym
