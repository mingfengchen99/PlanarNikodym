import PlanarNikodym.Analysis.Maximal.E2IntervalMaximalLipschitz
import PlanarNikodym.Analysis.Maximal.E2LpTestDensity
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! The genuine ambient Lᵖ extension of Definition 1.3 itself, on its
original compact parameter domain and original closed time interval. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

theorem Family.intervalMaximalComplex_e2_memLp {d : ℕ} (G : Family 2 d)
    (hG : G.IsSmooth) (K : Set (Parameters 2 d)) (hK : IsCompact K) (hKW : K ⊆ G.W)
    {p : ℝ≥0∞} {C : ℝ≥0} {f : Plane → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfp : MemLp f p volume)
    (hb : eLpNorm (G.intervalMaximal_e2 K f) p volume ≤ C * eLpNorm f p volume) :
    MemLp (G.intervalMaximalComplex_e2 K f) p volume := by
  obtain ⟨x₀, hx₀⟩ := hf.norm.exists_forall_ge_of_hasCompactSupport hfc.norm
  refine ⟨(G.intervalMaximalComplex_e2_measurable hG K hK hKW hf hx₀).aestronglyMeasurable, ?_⟩
  rw [G.intervalMaximalComplex_e2_eLpNorm K hx₀]
  exact hb.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hfp.eLpNorm_lt_top)

theorem Family.exists_intervalMaximal_Lp_extension_e2 {d : ℕ} (G : Family 2 d)
    (hG : G.IsSmooth) (K : Set (Parameters 2 d)) (hK : IsCompact K) (hKW : K ⊆ G.W)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (C : ℝ≥0)
    (hbound : ∀ f : Plane → ℂ, Continuous f → HasCompactSupport f → MemLp f p volume →
      eLpNorm (G.intervalMaximal_e2 K f) p volume ≤ C * eLpNorm f p volume) :
    ∃ T : Lp ℂ p (volume : Measure Plane) → Lp ℂ p (volume : Measure (Base 2)),
      LipschitzWith C T ∧ T 0 = 0 ∧ (∀ u, ‖T u‖ ≤ C * ‖u‖) ∧
      ∀ (f : Plane → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
        (hfp : MemLp f p volume),
        (T (hfp.toLp f) : Base 2 → ℂ) =ᵐ[volume] G.intervalMaximalComplex_e2 K f := by
  let R := compactContinuousLpTestRep_e2 (p := p)
  have hRcont (u : compactContinuousLpTests_e2 p) : Continuous (R u) :=
    (compactContinuousLpTestRep_e2_spec u).1
  have hRc (u : compactContinuousLpTests_e2 p) : HasCompactSupport (R u) :=
    (compactContinuousLpTestRep_e2_spec u).2.1
  have hRp (u : compactContinuousLpTests_e2 p) : MemLp (R u) p volume :=
    compactContinuousLpTestRep_e2_memLp u
  have hRT (u : compactContinuousLpTests_e2 p) :
      MemLp (G.intervalMaximalComplex_e2 K (R u)) p volume :=
    G.intervalMaximalComplex_e2_memLp hG K hK hKW (hRcont u) (hRc u) (hRp u)
      (hbound (R u) (hRcont u) (hRc u) (hRp u))
  let F : compactContinuousLpTests_e2 p → Lp ℂ p (volume : Measure (Base 2)) :=
    fun u => (hRT u).toLp (G.intervalMaximalComplex_e2 K (R u))
  have hFlip : LipschitzWith C F := by
    intro u v
    obtain ⟨Bu, hBu⟩ := compactContinuousLpTestRep_e2_bounded u
    obtain ⟨Bv, hBv⟩ := compactContinuousLpTestRep_e2_bounded v
    have hBd : ∀ x, ‖(R u - R v) x‖ ≤ Bu + Bv := fun x =>
      (norm_sub_le (R u x) (R v x)).trans (add_le_add (hBu x) (hBv x))
    have hinput : eLpNorm (R u - R v) p volume = edist u v := by
      change eLpNorm (R u - R v) p volume = edist u.val v.val
      rw [← compactContinuousLpTestRep_e2_toLp u, ← compactContinuousLpTestRep_e2_toLp v,
        Lp.edist_toLp_toLp]
    change edist ((hRT u).toLp _) ((hRT v).toLp _) ≤ _
    rw [Lp.edist_toLp_toLp]
    calc
      _ ≤ eLpNorm (G.intervalMaximalComplex_e2 K (R u - R v)) p volume := by
        apply eLpNorm_mono
        intro z
        exact G.intervalMaximalComplex_e2_norm_sub_le hG K hKW (hRcont u) (hRcont v) hBu hBv z
      _ = eLpNorm (G.intervalMaximal_e2 K (R u - R v)) p volume :=
        G.intervalMaximalComplex_e2_eLpNorm K hBd p
      _ ≤ C * eLpNorm (R u - R v) p volume :=
        hbound (R u - R v) ((hRcont u).sub (hRcont v)) ((hRc u).sub (hRc v)) ((hRp u).sub (hRp v))
      _ = _ := by rw [hinput]
  have hdense := compactContinuousLpTests_e2_dense p hp
  let T := hdense.extend F
  have hTlip : LipschitzWith C T := hdense.lipschitzWith_extend hFlip
  have hagree (f : Plane → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
      (hfp : MemLp f p volume) :
      (T (hfp.toLp f) : Base 2 → ℂ) =ᵐ[volume] G.intervalMaximalComplex_e2 K f := by
    let u : compactContinuousLpTests_e2 p := ⟨hfp.toLp f, f, hf, hfc, hfp, rfl⟩
    have hrepLp : (hRp u).toLp (R u) = hfp.toLp f := compactContinuousLpTestRep_e2_toLp u
    have hrep : R u = f := Measure.eq_of_ae_eq
      ((MemLp.toLp_eq_toLp_iff (hRp u) hfp).mp hrepLp) (hRcont u) hf
    have he : T (hfp.toLp f) = F u := hdense.extend_of_ind hFlip.uniformContinuous u
    rw [he]
    change ((hRT u).toLp (G.intervalMaximalComplex_e2 K (R u)) : Base 2 → ℂ) =ᵐ[volume] _
    simpa only [hrep] using (hRT u).coeFn_toLp
  have hTzero : T 0 = 0 := by
    have he := hagree 0 continuous_zero (by simpa using (HasCompactSupport.zero :
      HasCompactSupport (0 : Plane → ℂ))) (MemLp.zero (p := p))
    apply Lp.ext
    have he' : (T 0 : Base 2 → ℂ) =ᵐ[volume] 0 := by
      simpa only [MemLp.toLp_zero, G.intervalMaximalComplex_e2_zero] using he
    exact he'.trans (Lp.coeFn_zero ℂ p (volume : Measure (Base 2))).symm
  refine ⟨T, hTlip, hTzero, ?_, hagree⟩
  intro u
  have hh := hTlip.dist_le_mul u 0
  simpa only [hTzero, dist_zero_right] using hh

theorem Family.intervalMaximal_Lp_extension_unique_e2 {d : ℕ} (G : Family 2 d)
    (K : Set (Parameters 2 d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {T S : Lp ℂ p (volume : Measure Plane) → Lp ℂ p (volume : Measure (Base 2))}
    (hT : Continuous T) (hS : Continuous S)
    (hTagree : ∀ (f : Plane → ℂ) (_hf : Continuous f) (_hc : HasCompactSupport f)
      (hfp : MemLp f p volume),
      (T (hfp.toLp f) : Base 2 → ℂ) =ᵐ[volume] G.intervalMaximalComplex_e2 K f)
    (hSagree : ∀ (f : Plane → ℂ) (_hf : Continuous f) (_hc : HasCompactSupport f)
      (hfp : MemLp f p volume),
      (S (hfp.toLp f) : Base 2 → ℂ) =ᵐ[volume] G.intervalMaximalComplex_e2 K f) : T = S := by
  apply (compactContinuousLpTests_e2_dense p hp).denseRange_val.equalizer hT hS
  funext u
  have hu := compactContinuousLpTestRep_e2_spec u
  have ht := hTagree (compactContinuousLpTestRep_e2 u) hu.1 hu.2.1
    (compactContinuousLpTestRep_e2_memLp u)
  have hs := hSagree (compactContinuousLpTestRep_e2 u) hu.1 hu.2.1
    (compactContinuousLpTestRep_e2_memLp u)
  rw [compactContinuousLpTestRep_e2_toLp] at ht hs
  exact Lp.ext (ht.trans hs.symm)

end PlanarNikodym
