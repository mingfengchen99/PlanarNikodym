import PlanarNikodym.Analysis.Fourier.FourierCharacterJets
import PlanarNikodym.Analysis.Jets.CompactTimeJets

/-! Actual frequency derivatives of the oscillatory time amplitude.
Compactness bounds the spatial graph on the support and gives constants
uniform in the frequency and all curve parameters. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace PlanarNikodym

theorem planeFourierCharacter_symm (x ξ : Plane) :
    planeFourierCharacter x ξ = planeFourierCharacter ξ x := by
  unfold planeFourierCharacter
  congr 3
  unfold fourierPhase
  ring

theorem planeFourierCharacter_frequency_contDiff (x : Plane) :
    ContDiff ℝ ∞ (fun ξ => planeFourierCharacter x ξ) := by
  simpa only [planeFourierCharacter_symm x] using planeFourierCharacter_contDiff x

theorem contDiff_planeFourierCharacter :
    ContDiff ℝ ∞ (fun p : Plane × Plane => planeFourierCharacter p.1 p.2) := by
  unfold planeFourierCharacter fourierPhase
  have hreal : ContDiff ℝ ∞ (fun p : Plane × Plane =>
      2 * Real.pi * (p.1.1 * p.2.1 + p.1.2 * p.2.2)) := by fun_prop
  exact ((Complex.ofRealCLM.contDiff.comp hreal).mul contDiff_const).cexp

theorem norm_iteratedFDeriv_planeFourierCharacter_frequency_le
    (x ξ : Plane) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun η => planeFourierCharacter x η) ξ‖ ≤
      (2 * Real.pi * (|x.1| + |x.2|)) ^ m := by
  have he : (fun η => planeFourierCharacter x η) = fun η => planeFourierCharacter η x :=
    funext (planeFourierCharacter_symm x)
  rw [he]
  exact norm_iteratedFDeriv_planeFourierCharacter_le x ξ m

def Family.cutoffOscillatoryFrequencyIntegrand {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (q : Parameters 2 d) (p : Plane × ℝ) : ℂ :=
  (χ (p.2, q) : ℂ) * planeFourierCharacter (G.graphMap q p.2) p.1

theorem Family.contDiff_cutoffOscillatoryFrequencyIntegrand {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (q : Parameters 2 d) :
    ContDiff ℝ ∞ (G.cutoffOscillatoryFrequencyIntegrand χ q) := by
  have hemb : ContDiff ℝ ∞ (fun p : Plane × ℝ => (p.2, q)) :=
    contDiff_snd.prodMk contDiff_const
  have hcut : ContDiff ℝ ∞ (fun p : Plane × ℝ => (χ (p.2, q) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hχ.comp hemb)
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hx : (p.2, q) ∈ tsupport χ
  · have hgraph : ContDiffAt ℝ ∞ (fun p : Plane × ℝ => G.graphMap q p.2) p :=
      contDiffAt_snd.prodMk
        ((hγ (p.2, q) hx).comp (f := fun p : Plane × ℝ => (p.2, q)) p hemb.contDiffAt)
    exact hcut.contDiffAt.mul
      (contDiff_planeFourierCharacter.contDiffAt.comp p (hgraph.prodMk contDiffAt_fst))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    have he : ∀ᶠ y in 𝓝 p, (y.2, q) ∉ tsupport χ :=
      hemb.continuous.continuousAt.eventually
        ((isClosed_tsupport χ).isOpen_compl.mem_nhds hx)
    filter_upwards [he] with y hy
    simp only [Family.cutoffOscillatoryFrequencyIntegrand,
      image_eq_zero_of_notMem_tsupport hy, Complex.ofReal_zero, zero_mul]

theorem Family.cutoffOscillatoryFrequencyIntegrand_eq_zero_off_time_support
    {d : ℕ} (G : Family 2 d) (χ : Cutoff d) (q : Parameters 2 d)
    (ξ : Plane) (t : ℝ) (ht : t ∉ Prod.fst '' tsupport χ) :
    G.cutoffOscillatoryFrequencyIntegrand χ q (ξ, t) = 0 := by
  have hx : (t, q) ∉ tsupport χ := fun hx => ht ⟨(t, q), hx, rfl⟩
  simp only [Family.cutoffOscillatoryFrequencyIntegrand,
    image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero, zero_mul]

theorem Family.cutoffOscillatoryAmplitude_frequency_contDiff {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (q : Parameters 2 d) :
    ContDiff ℝ ∞ (G.cutoffOscillatoryAmplitude χ q) := by
  exact contDiff_integral_of_compact_time_support
    (G.contDiff_cutoffOscillatoryFrequencyIntegrand χ hχ hγ q)
    (hc.isCompact.image continuous_fst)
    (G.cutoffOscillatoryFrequencyIntegrand_eq_zero_off_time_support χ q)

theorem Family.cutoffOscillatoryFrequencyIntegrand_jet_eq {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (q : Parameters 2 d) (m : ℕ) (ξ : Plane) (t : ℝ) :
    iteratedFDeriv ℝ m (fun η => G.cutoffOscillatoryFrequencyIntegrand χ q (η, t)) ξ =
      (χ (t, q) : ℂ) • iteratedFDeriv ℝ m
        (fun η => planeFourierCharacter (G.graphMap q t) η) ξ := by
  exact iteratedFDeriv_const_smul_apply' (a := (χ (t, q) : ℂ))
    (contDiff_infty.mp (planeFourierCharacter_frequency_contDiff (G.graphMap q t)) m).contDiffAt

/-- Every complete frequency derivative is the time integral of the
complete derivative of the actual Fourier character. -/
theorem Family.cutoffOscillatoryAmplitude_frequency_jet_eq_integral {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (q : Parameters 2 d) (m : ℕ) (ξ : Plane) :
    iteratedFDeriv ℝ m (G.cutoffOscillatoryAmplitude χ q) ξ =
      ∫ t : ℝ, (χ (t, q) : ℂ) • iteratedFDeriv ℝ m
        (fun η => planeFourierCharacter (G.graphMap q t) η) ξ := by
  change iteratedFDeriv ℝ m
    (fun η => ∫ t : ℝ, G.cutoffOscillatoryFrequencyIntegrand χ q (η, t)) ξ = _
  rw [iteratedFDeriv_integral_of_compact_time_support m
    (G.contDiff_cutoffOscillatoryFrequencyIntegrand χ hχ hγ q)
    (hc.isCompact.image continuous_fst)
    (G.cutoffOscillatoryFrequencyIntegrand_eq_zero_off_time_support χ q) ξ]
  exact integral_congr_ae (ae_of_all _
    (fun t => G.cutoffOscillatoryFrequencyIntegrand_jet_eq χ q m ξ t))

theorem Family.cutoffOscillatoryFrequencyJet_integrable {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (q : Parameters 2 d) (m : ℕ) (ξ : Plane) :
    Integrable (fun t : ℝ => (χ (t, q) : ℂ) • iteratedFDeriv ℝ m
      (fun η => planeFourierCharacter (G.graphMap q t) η) ξ) :=
  (integrable_parameter_iteratedFDeriv_of_compact_time_support m
    (G.contDiff_cutoffOscillatoryFrequencyIntegrand χ hχ hγ q)
    (hc.isCompact.image continuous_fst)
    (G.cutoffOscillatoryFrequencyIntegrand_eq_zero_off_time_support χ q) ξ).congr
    (ae_of_all _ (fun t => G.cutoffOscillatoryFrequencyIntegrand_jet_eq χ q m ξ t))

/-- Spatial compactness on the cutoff support bounds all frequency jets,
uniformly over every curve parameter and every frequency. -/
theorem Family.exists_uniform_cutoffOscillatoryAmplitude_frequency_jet_bound
    {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : Parameters 2 d) (ξ : Plane),
      ‖iteratedFDeriv ℝ m (G.cutoffOscillatoryAmplitude χ q) ξ‖ ≤ C := by
  classical
  have hgraph : ContinuousOn (fun x : ℝ × Parameters 2 d => G.graphMap x.2 x.1)
      (tsupport χ) := by
    intro x hx
    exact (continuousAt_fst.prodMk (hγ x hx).continuousAt).continuousWithinAt
  obtain ⟨B, hB⟩ := hc.isCompact.exists_bound_of_continuousOn hgraph
  obtain ⟨x₀, hx₀⟩ := hχ.continuous.norm.exists_forall_ge_of_hasCompactSupport hc.norm
  let R : ℝ := |B| + 1
  let M : ℝ := 1 + ‖χ x₀‖
  let T : Set ℝ := Prod.fst '' tsupport χ
  let A : ℝ := M * (4 * Real.pi * R) ^ m
  have hR : 0 < R := by dsimp [R]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hT : IsCompact T := hc.isCompact.image continuous_fst
  refine ⟨A * (volume.real T + 1), mul_pos hA (by positivity), ?_⟩
  intro q ξ
  have hi : Integrable (T.indicator (fun _ => A)) :=
    (integrableOn_const hT.measure_ne_top).integrable_indicator hT.measurableSet
  have hpoint (t : ℝ) :
      ‖(χ (t, q) : ℂ) • iteratedFDeriv ℝ m
        (fun η => planeFourierCharacter (G.graphMap q t) η) ξ‖ ≤
        T.indicator (fun _ => A) t := by
    by_cases hx : (t, q) ∈ tsupport χ
    · have ht : t ∈ T := ⟨(t, q), hx, rfl⟩
      rw [indicator_of_mem ht, norm_smul]
      have hχnorm : ‖(χ (t, q) : ℂ)‖ ≤ M := by
        simpa only [Complex.norm_real, M] using (hx₀ (t, q)).trans
          (le_add_of_nonneg_left zero_le_one)
      have hgraphB : ‖G.graphMap q t‖ ≤ R := (hB (t, q) hx).trans (by
        dsimp [R]; linarith [le_abs_self B])
      have hcoords : |(G.graphMap q t).1| + |(G.graphMap q t).2| ≤ 2 * R := by
        have h₁ := norm_fst_le (G.graphMap q t)
        have h₂ := norm_snd_le (G.graphMap q t)
        simp only [Real.norm_eq_abs] at h₁ h₂
        linarith
      have hf : ‖iteratedFDeriv ℝ m
          (fun η => planeFourierCharacter (G.graphMap q t) η) ξ‖ ≤ (4 * Real.pi * R) ^ m := by
        apply (norm_iteratedFDeriv_planeFourierCharacter_frequency_le (G.graphMap q t) ξ m).trans
        apply pow_le_pow_left₀ (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left hcoords Real.pi_pos.le]
      exact mul_le_mul hχnorm hf (norm_nonneg _) hM.le
    · rw [image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero, zero_smul, norm_zero]
      exact indicator_nonneg (fun _ _ => hA.le) t
  rw [G.cutoffOscillatoryAmplitude_frequency_jet_eq_integral χ hχ hc hγ q m ξ]
  calc
    _ ≤ ∫ t : ℝ, ‖(χ (t, q) : ℂ) • iteratedFDeriv ℝ m
        (fun η => planeFourierCharacter (G.graphMap q t) η) ξ‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, T.indicator (fun _ => A) t := integral_mono
      (G.cutoffOscillatoryFrequencyJet_integrable χ hχ hc hγ q m ξ).norm hi hpoint
    _ = volume.real T * A := by rw [integral_indicator_const _ hT.measurableSet, smul_eq_mul]
    _ ≤ A * (volume.real T + 1) := by nlinarith

/-- Dilation by any real frequency scale costs exactly the expected
power of its absolute value, including scale zero. -/
theorem Family.exists_uniform_cutoffOscillatoryAmplitude_scaled_frequency_jet_bound
    {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : Parameters 2 d) (r : ℝ) (ξ : Plane),
      ‖iteratedFDeriv ℝ m (fun η => G.cutoffOscillatoryAmplitude χ q (r • η)) ξ‖ ≤
        C * |r| ^ m := by
  obtain ⟨C, hC, hbound⟩ :=
    G.exists_uniform_cutoffOscillatoryAmplitude_frequency_jet_bound χ hχ hc hγ m
  refine ⟨C, hC, ?_⟩
  intro q r ξ
  have he := congrFun (iteratedFDeriv_comp_const_smul r
    (contDiff_infty.mp (G.cutoffOscillatoryAmplitude_frequency_contDiff χ hχ hc hγ q) m)) ξ
  rw [he, norm_smul, Real.norm_eq_abs, abs_pow]
  calc
    |r| ^ m * ‖iteratedFDeriv ℝ m (G.cutoffOscillatoryAmplitude χ q) (r • ξ)‖ ≤
        |r| ^ m * C := mul_le_mul_of_nonneg_left (hbound q (r • ξ)) (by positivity)
    _ = _ := mul_comm _ _

end PlanarNikodym
