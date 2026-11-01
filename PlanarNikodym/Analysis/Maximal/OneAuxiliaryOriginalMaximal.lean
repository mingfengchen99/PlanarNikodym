import PlanarNikodym.Analysis.Maximal.OneAuxiliaryExponentRange
import PlanarNikodym.Analysis.Maximal.E2ClosedSmoothPhaseTransport

/-! The d=1 branch of the original Theorem 1.1, on the original closed
time interval and arbitrary compact parameter set. The original maximal
operator has a genuine Lp extension for every p>2. No geometric endpoint
or extra analytic Input remains in the hypotheses. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal NNReal
namespace PlanarNikodym

theorem Family.one_auxiliary_compact_maximal_bound (G : Family 2 1)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 1 => G.γ x.1 x.2))
    (K : Set (Parameters 2 1)) (hK : IsCompact K) (hKW : K ⊆ G.W)
    (hd : ∀ t ∈ G.I.carrier, ∀ q ∈ K, G.cinematicDet (t,q) ≠ 0)
    (L : FrequencyCutoff) (p : ℝ≥0) (hp : 2 < p) :
    ∃ C : ℝ≥0, ∀ f : Plane → ℂ, Continuous f → HasCompactSupport f → MemLp f p volume →
      Measurable (G.intervalMaximal_e2 K f) ∧
        eLpNorm (G.intervalMaximal_e2 K f) p volume ≤ C * eLpNorm f p volume := by
  obtain ⟨χ,hχ,hc,hr,hχ1,hdet⟩ := G.exists_compact_interval_cutoff_e2 hG K hK hd
  obtain ⟨η,hη,CH,hCH⟩ := G.one_auxiliary_summable_dyadic_estimate
    hG χ hχ hc (fun x => (hr x).1) hdet L p hp
  obtain ⟨C,hC⟩ := G.cutoffMaximal_continuous_tests_of_summable_dyadic_e2 χ hχ.continuous hc
    (fun _ _ => hG.continuous.continuousAt) L p (by linarith) hη CH hCH
  refine ⟨C,?_⟩
  intro f hf hfc hfp
  apply G.intervalMaximal_e2_bound_of_cutoff hG.contDiffOn K hK hKW χ hχ.continuous hc
    (fun _ _ => hG.continuous.continuousAt) (fun x => (hr x).1)
    (fun t ht q hq => (hχ1 t ht q hq).symm.le) p C
    (fun f hf hfc hfp => ?_) hf hfc hfp
  obtain ⟨x₀,hx₀⟩ := hf.norm.exists_forall_ge_of_hasCompactSupport hfc.norm
  exact (hC f hf (hf.integrable_of_hasCompactSupport hfc) hfp ⟨‖f x₀‖,hx₀⟩).2

theorem Family.one_auxiliary_compact_maximal_Lp_extension (G : Family 2 1)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 1 => G.γ x.1 x.2))
    (K : Set (Parameters 2 1)) (hK : IsCompact K) (hKW : K ⊆ G.W)
    (hd : ∀ t ∈ G.I.carrier, ∀ q ∈ K, G.cinematicDet (t,q) ≠ 0)
    (L : FrequencyCutoff) (p : ℝ≥0) [Fact (1 ≤ (p : ℝ≥0∞))] (hp : 2 < p) :
    ∃ C : ℝ≥0, ∃ T : Lp ℂ p (volume : Measure Plane) → Lp ℂ p (volume : Measure (Base 2)),
      LipschitzWith C T ∧ T 0 = 0 ∧ (∀ u, ‖T u‖ ≤ C * ‖u‖) ∧
      ∀ (f : Plane → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
        (hfp : MemLp f p volume),
        (T (hfp.toLp f) : Base 2 → ℂ) =ᵐ[volume] G.intervalMaximalComplex_e2 K f := by
  obtain ⟨C,hC⟩ := G.one_auxiliary_compact_maximal_bound hG K hK hKW hd L p hp
  exact ⟨C,G.exists_intervalMaximal_Lp_extension_e2 hG.contDiffOn K hK hKW p
    ENNReal.coe_ne_top C (fun f hf hfc hfp => (hC f hf hfc hfp).2)⟩

theorem Family.theorem_1_1_one_auxiliary_proved (G : Family 2 1)
    (hW : IsOpen G.W) (hG : G.IsSmooth)
    (K : Set (Parameters 2 1)) (hK : IsCompact K) (hKW : K ⊆ G.W)
    (hd : ∀ t ∈ G.I.carrier, ∀ q ∈ K, G.cinematicDetWithin_e2 (t,q) ≠ 0)
    (p : ℝ≥0) (hp : 2 < p) :
    letI : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast (show (1 : ℝ≥0) ≤ p by linarith)⟩
    ∃ C : ℝ≥0, ∃ T : Lp ℂ p (volume : Measure Plane) → Lp ℂ p (volume : Measure (Base 2)),
      LipschitzWith C T ∧ T 0 = 0 ∧ (∀ u, ‖T u‖ ≤ C * ‖u‖) ∧
      ∀ (f : Plane → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
        (hfp : MemLp f p volume),
        (T (hfp.toLp f) : Base 2 → ℂ) =ᵐ[volume] G.intervalMaximalComplex_e2 K f := by
  letI : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast (show (1 : ℝ≥0) ≤ p by linarith)⟩
  obtain ⟨H,hI,hHW,hH,hjet,hmax⟩ :=
    G.exists_compact_closed_smooth_extension_e2 hW hG K hK hKW
  have hKH : K ⊆ H.W := by rwa [hHW]
  have hHd : ∀ t ∈ H.I.carrier, ∀ q ∈ K, H.cinematicDet (t,q) ≠ 0 := by
    intro t ht q hq
    have htG : t ∈ G.I.carrier := by rwa [hI] at ht
    unfold cinematicDet
    rw [hjet (t,q) ⟨htG,hq⟩]
    exact hd t htG q hq
  obtain ⟨C,T,hLip,hzero,hbound,hagree⟩ :=
    H.one_auxiliary_compact_maximal_Lp_extension hH K hK hKH hHd standardFrequencyCutoff p hp
  refine ⟨C,T,hLip,hzero,hbound,?_⟩
  intro f hf hfc hfp
  have he : H.intervalMaximalComplex_e2 K f = G.intervalMaximalComplex_e2 K f := by
    funext z
    unfold intervalMaximalComplex_e2
    rw [hmax f]
  rw [← he]
  exact hagree f hf hfc hfp

theorem Family.theorem_1_1_one_auxiliary_ambient_jets (G : Family 2 1)
    (hW : IsOpen G.W) (hG : G.IsSmooth)
    (K : Set (Parameters 2 1)) (hK : IsCompact K) (hKW : K ⊆ G.W)
    (hGreg : ∀ x ∈ G.I.carrier ×ˢ K,
      ContDiffAt ℝ 3 (fun y : ℝ × Parameters 2 1 => G.γ y.1 y.2) x)
    (hd : ∀ t ∈ G.I.carrier, ∀ q ∈ K, G.cinematicDet (t,q) ≠ 0)
    (p : ℝ≥0) (hp : 2 < p) :
    letI : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast (show (1 : ℝ≥0) ≤ p by linarith)⟩
    ∃ C : ℝ≥0, ∃ T : Lp ℂ p (volume : Measure Plane) → Lp ℂ p (volume : Measure (Base 2)),
      LipschitzWith C T ∧ T 0 = 0 ∧ (∀ u, ‖T u‖ ≤ C * ‖u‖) ∧
      ∀ (f : Plane → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
        (hfp : MemLp f p volume),
        (T (hfp.toLp f) : Base 2 → ℂ) =ᵐ[volume] G.intervalMaximalComplex_e2 K f := by
  letI : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast (show (1 : ℝ≥0) ≤ p by linarith)⟩
  apply G.theorem_1_1_one_auxiliary_proved hW hG K hK hKW _ p hp
  intro t ht q hq
  rw [G.cinematicDetWithin_e2_eq_ambient hW ⟨ht,hKW hq⟩ (hGreg (t,q) ⟨ht,hq⟩)]
  exact hd t ht q hq

end PlanarNikodym
