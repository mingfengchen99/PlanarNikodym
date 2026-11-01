import PlanarNikodym.Analysis.Fourier.FullCinematicMainLpTransport

/-! The complete original cutoff has a uniform smallest-piece Lp
endpoint in all output parameters, with no selected-fiber assumption. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff BigOperators
namespace PlanarNikodym

theorem Family.fullFiniteSliceMain_sum_cutoff {d : ℕ} {ι : Type*} [Fintype ι]
    (G : Family 2 d) (χ : Cutoff d) (ψ : ι → Cutoff d)
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (hc : ∀ i, HasCompactSupport (ψ i))
    (hγ : ∀ i x, x ∈ tsupport (ψ i) →
      ContinuousAt (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (hsum : ∀ x, ∑ i, ψ i x = χ x)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : Continuous β)
    (r b δ : ℝ) (N : ℕ) {f : Plane → ℂ} (hf : Integrable f) :
    G.fullFiniteSliceMain χ L β r b δ N f =
      ∑ i, G.fullFiniteSliceMain (ψ i) L β r b δ N f := by
  funext w
  have he : scaleTimeLocalizedCutoff χ b δ w.1.val =
      fun x => ∑ i, scaleTimeLocalizedCutoff (ψ i) b δ w.1.val x := by
    funext x
    simp only [scaleTimeLocalizedCutoff, ← Finset.sum_mul, hsum]
  change G.cutoffPartialExtension (scaleTimeLocalizedCutoff χ b δ w.1.val) L β r f w.2 = _
  rw [he, G.cutoffPartialExtension_sum_cutoff
    (fun i => scaleTimeLocalizedCutoff (ψ i) b δ w.1.val)
    (fun i => (contDiff_scaleTimeLocalizedCutoff (hψ i) b δ w.1.val).continuous)
    (fun i => hasCompactSupport_scaleTimeLocalizedCutoff (hc i) b δ w.1.val)
    (fun i x hx => hγ i x (tsupport_scaleTimeLocalizedCutoff_subset (ψ i) b δ w.1.val hx))
    L hβ hf r w.2]
  simp only [Finset.sum_apply, Family.fullFiniteSliceMain]

/-- Every p>2 admits the actual full-parameter r^(-1/2) endpoint.
The constant precedes the time translate, number of pieces, frequency
and input, and the same original cutoff occurs on the left. -/
theorem Family.exists_full_cinematic_critical_main_Lp_decay {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (ha : ∀ x ∈ tsupport χ, AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    (hdet : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (F : FrequencyCutoff) (βfreq : ℝ → ℝ) (hβfreq : ContDiff ℝ ∞ βfreq)
    {p : ℝ≥0} (hp : 2 < p) {κ : ℝ} (hκ : 0 < κ)
    (hgap : ∀ ξ : Plane, |ξ.2| < κ → F.bandSymbol 0 ξ * βfreq ξ.2 = 0) :
    ∃ C R : ℝ, 0 ≤ C ∧ 1 ≤ R ∧ ∀ (b : ℝ) (N : ℕ) (f : Plane → ℂ),
      Integrable f → MemLp f p volume → ∀ r : ℝ, R ≤ r →
      let δ := criticalTimeScale 1 (2 * Real.pi * r)
      eLpNorm (G.fullFiniteSliceMain χ F βfreq r b δ N f) p
        (fullFiniteSliceMainMeasure d N) ≤
        ENNReal.ofReal (C * r ^ (-(1 / 2 : ℝ))) * eLpNorm f p volume := by
  classical
  obtain ⟨I, ψ, σ, R, hR, hsum, hpatch⟩ :=
    G.exists_finite_cinematic_critical_main_Lp_decay_partition χ hχ hc hχ0 ha hdet F βfreq hβfreq
  have hpR : (2 : ℝ) < p := by exact_mod_cast hp
  have hp0 : 0 < p := (by norm_num : (0 : ℝ≥0) < 2).trans hp
  have hlocal (i : I) := (hpatch i).2.2.2 (p : ℝ) hpR κ hκ hgap
  choose C hC hb using hlocal
  have hvolume (i : I) := exists_full_finite_fiber_norm_factor (σ i)
    ((parameterFrame d).symm i.val.val.2) (tsupport (ψ i)) (hpatch i).2.1
  choose V hV hv using hvolume
  let A := fun i : I => V i ^ (1 / (p : ℝ)) * C i
  have hA (i : I) : 0 ≤ A i := mul_nonneg (Real.rpow_nonneg (hV i).le _) (hC i)
  refine ⟨∑ i, A i, R, Finset.sum_nonneg (fun i _ => hA i), hR, ?_⟩
  intro b N f hf hfp r hr
  let δ := criticalTimeScale 1 (2 * Real.pi * r)
  let H := fun i : I => G.fullFiniteSliceMain (ψ i) F βfreq r b δ N f
  have hm (i : I) : Measurable (H i) := G.measurable_fullFiniteSliceMain (ψ i)
    (hpatch i).1.continuous (hpatch i).2.1
    (fun x hx => ha x ((hpatch i).2.2.1 hx)) F βfreq hβfreq.continuous r b δ N hf
  have hi (i : I) : eLpNorm (H i) p (fullFiniteSliceMainMeasure d N) ≤
      ENNReal.ofReal (A i * r ^ (-(1 / 2 : ℝ))) * eLpNorm f p volume := by
    have hh := hv i N (H i) (hm i)
      (G.fullFiniteSliceMain_support (ψ i) F βfreq r b δ N f) p hp0
      (ENNReal.ofReal (C i * r ^ (-(1 / 2 : ℝ))) * eLpNorm f p volume) (fun u => ?_)
    · apply hh.trans_eq
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg (hV i).le _)]
      congr 2
      dsimp only [A]
      ring
    · have hb' := hb i b N u f hf
        (by simpa only [ENNReal.ofReal_coe_nnreal] using hfp) r hr
      dsimp only at hb'
      unfold Family.finiteSliceMain at hb'
      simpa only [ENNReal.ofReal_coe_nnreal, H, Family.fullFiniteSliceMain,
        glyzFiberParameter, glyzFiberBase, δ] using hb'
  have he := G.fullFiniteSliceMain_sum_cutoff χ ψ (fun i => (hpatch i).1)
    (fun i => (hpatch i).2.1)
    (fun i x hx => (ha x ((hpatch i).2.2.1 hx)).continuousAt)
    hsum F βfreq hβfreq.continuous r b δ N hf
  change eLpNorm (G.fullFiniteSliceMain χ F βfreq r b δ N f) p _ ≤ _
  rw [he]
  calc
    _ ≤ ∑ i : I, eLpNorm (H i) p (fullFiniteSliceMainMeasure d N) :=
      eLpNorm_sum_le (fun i _ => (hm i).aestronglyMeasurable) (by exact_mod_cast hp.le.trans' (by norm_num : (1 : ℝ≥0) ≤ 2))
    _ ≤ ∑ i : I, ENNReal.ofReal (A i * r ^ (-(1 / 2 : ℝ))) * eLpNorm f p volume :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg
        (fun i _ => mul_nonneg (hA i) (Real.rpow_nonneg (zero_lt_one.trans_le (hR.trans hr)).le _)),
        ← Finset.sum_mul]

end PlanarNikodym
