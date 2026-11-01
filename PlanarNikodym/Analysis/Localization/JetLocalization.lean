import PlanarNikodym.Analysis.Maximal.GeneralSmoothAnalysis
import PlanarNikodym.Analysis.Localization.FiniteCutoffPartition

/-! Finite localization of the actual average and every actual finite jet.
Local smoothing constants add over finitely many pieces, without a new
frequency loss. The local smoothing estimates themselves remain hypotheses. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal NNReal

namespace PlanarNikodym

theorem Family.cutoffAverage_sum_cutoff {d : ℕ} {ι : Type*} [Fintype ι]
    (G : Family 2 d) (ψ : ι → Cutoff d)
    (hψ : ∀ i, Continuous (ψ i)) (hc : ∀ i, HasCompactSupport (ψ i))
    (hγ : ∀ i x, x ∈ tsupport (ψ i) →
      ContinuousAt (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : Continuous f) (q : Parameters 2 d) :
    G.cutoffAverage (fun x => ∑ i, ψ i x) f q = ∑ i, G.cutoffAverage (ψ i) f q := by
  classical
  unfold cutoffAverage
  simp only [Complex.ofReal_sum, Finset.sum_mul]
  exact integral_finsetSum Finset.univ
    (fun i _ => G.cutoffIntegrand_integrable (ψ i) (hψ i) (hc i) (hγ i) hf q)

theorem Family.auxiliaryJetNorm_sum_cutoff_le {d : ℕ} {ι : Type*} [Fintype ι]
    (G : Family 2 d) (ψ : ι → Cutoff d)
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (hc : ∀ i, HasCompactSupport (ψ i))
    (hγ : ∀ i x, x ∈ tsupport (ψ i) →
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (p : ℝ≥0) (hp : 1 ≤ p) (j : ℕ) :
    G.auxiliaryJetNorm (fun x => ∑ i, ψ i x) f p j ≤
      ∑ i, G.auxiliaryJetNorm (ψ i) f p j := by
  classical
  have hA (i : ι) : ContDiff ℝ ∞ (G.cutoffAverage (ψ i) f) :=
    G.cutoffAverage_contDiff (ψ i) (hψ i) (hc i) (hγ i) hf
  let J : ι → Parameters 2 d → (Aux d [×j]→L[ℝ] ℂ) :=
    fun i q => iteratedFDeriv ℝ j (fun u => G.cutoffAverage (ψ i) f (q.1, u)) q.2
  have hsum : (fun q : Parameters 2 d => iteratedFDeriv ℝ j
      (fun u => G.cutoffAverage (fun x => ∑ i, ψ i x) f (q.1, u)) q.2) = ∑ i, J i := by
    funext q
    have heq : (fun u => G.cutoffAverage (fun x => ∑ i, ψ i x) f (q.1, u)) =
        fun u => ∑ i, G.cutoffAverage (ψ i) f (q.1, u) := by
      funext u
      exact G.cutoffAverage_sum_cutoff ψ (fun i => (hψ i).continuous) hc
        (fun i x hx => (hγ i x hx).continuousAt) hf.continuous (q.1, u)
    rw [heq, Finset.sum_apply]
    exact iteratedFDeriv_fun_sum_apply (fun i _ =>
      (contDiff_infty.mp (hA i) j).contDiffAt.comp q.2
        (contDiffAt_const.prodMk contDiffAt_id))
  have hJ (i : ι) : AEStronglyMeasurable (J i) volume :=
    (continuous_auxiliary_iteratedFDeriv_of_smooth (hA i) j).aestronglyMeasurable
  unfold auxiliaryJetNorm
  rw [eLpNorm_norm, hsum]
  simpa only [eLpNorm_norm] using
    (eLpNorm_sum_le (s := Finset.univ) (f := J) (fun i _ => hJ i) (by exact_mod_cast hp))

theorem Family.scaledJetNorm_sum_cutoff_le {d : ℕ} {ι : Type*} [Fintype ι]
    (G : Family 2 d) (ψ : ι → Cutoff d)
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (hc : ∀ i, HasCompactSupport (ψ i))
    (hγ : ∀ i x, x ∈ tsupport (ψ i) →
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (p : ℝ≥0) (hp : 1 ≤ p) (s k : ℕ) :
    G.scaledJetNorm (fun x => ∑ i, ψ i x) f p s k ≤
      ∑ i, G.scaledJetNorm (ψ i) f p s k := by
  classical
  unfold scaledJetNorm
  calc
    _ ≤ ∑ j ∈ Finset.range (s + 1), dyadicWeight (-(j : ℝ)) k *
        ∑ i, G.auxiliaryJetNorm (ψ i) f p j := by
      apply Finset.sum_le_sum
      intro j _
      gcongr
      exact G.auxiliaryJetNorm_sum_cutoff_le ψ hψ hc hγ hf p hp j
    _ = _ := by simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]

/-- Finite patch estimates give the actual full cutoff estimate. The new
constant is exactly the sum of patch constants, independent of `k,f`. -/
theorem jetSmoothingInput_sum_cutoff {d : ℕ} {ι : Type*} [Fintype ι]
    (G : Family 2 d) (ψ : ι → Cutoff d)
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (hc : ∀ i, HasCompactSupport (ψ i))
    (hγ : ∀ i x, x ∈ tsupport (ψ i) →
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (p : ℝ≥0) (hp : 1 ≤ p) (s : ℕ) (ε : ℝ)
    (hS : ∀ i, JetSmoothingInput G (ψ i) L p s ε) :
    JetSmoothingInput G (fun x => ∑ i, ψ i x) L p s ε := by
  classical
  choose C hC using hS
  refine ⟨∑ i, C i, ?_⟩
  intro k f hi hf
  calc
    _ ≤ ∑ i, G.scaledJetNorm (ψ i) (L.band k f) p s k :=
      G.scaledJetNorm_sum_cutoff_le ψ hψ hc hγ (L.band_contDiff_infty k hi) p hp s k
    _ ≤ ∑ i, (C i : ℝ≥0∞) * dyadicWeight (-((d + 1 : ℕ) : ℝ) / (p : ℝ) + ε) k *
        eLpNorm f p volume := Finset.sum_le_sum (fun i _ => hC i k f hi hf)
    _ = _ := by simp only [ENNReal.ofNNReal_finsetSum, Finset.sum_mul]

/-- Ordinary pointwise small-support estimates suffice on any compact
cutoff support. The finite partition is constructed, not supplied as input. -/
theorem jetSmoothingInput_of_local_cutoffs {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (p : ℝ≥0) (hp : 1 ≤ p) (s : ℕ) (ε : ℝ)
    (hlocal : ∀ x ∈ tsupport χ, ∃ O : Set (ℝ × Parameters 2 d),
      IsOpen O ∧ x ∈ O ∧ ∀ ψ : Cutoff d, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ O → JetSmoothingInput G ψ L p s ε) :
    JetSmoothingInput G χ L p s ε := by
  classical
  have hloc : ∀ x : tsupport χ, ∃ O : Set (ℝ × Parameters 2 d),
      IsOpen O ∧ (x : ℝ × Parameters 2 d) ∈ O ∧
      ∀ ψ : Cutoff d, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ O → JetSmoothingInput G ψ L p s ε :=
    fun x => hlocal x x.2
  choose O hO hxO hE using hloc
  have hcover : tsupport χ ⊆ ⋃ x : tsupport χ, O x :=
    fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxO ⟨x, hx⟩⟩
  obtain ⟨S, ψ, hψ, hsum⟩ := exists_finite_cutoff_partition χ hχ hc hχ0 O hO hcover
  have h := jetSmoothingInput_sum_cutoff G ψ (fun i => (hψ i).1)
    (fun i => (hψ i).2.1) (fun i x hx => hγ x ((hψ i).2.2.1 hx)) L p hp s ε
    (fun i => hE i (ψ i) (hψ i).1 (hψ i).2.1 (hψ i).2.2.2.1)
  have heq : (fun x => ∑ i : S, ψ i x) = χ := funext hsum
  simpa only [heq] using h

end PlanarNikodym
