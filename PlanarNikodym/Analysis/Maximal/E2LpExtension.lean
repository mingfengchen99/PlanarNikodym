import PlanarNikodym.Analysis.Maximal.E2ContinuousMaximal
import PlanarNikodym.Analysis.Maximal.E2LpTestDensity
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! A genuine extension of the original maximal operator from compact
continuous tests to the complete ambient Lᵖ space. The extension agrees
with the original pointwise operator on every such test, almost everywhere.
It does not choose pointwise values of arbitrary ambient Lᵖ classes. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

theorem Family.cutoffMaximalComplex_e2_memLp {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {p : ℝ≥0∞} {C : ℝ≥0}
    {f : Plane → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (hfp : MemLp f p volume)
    (hb : eLpNorm (G.cutoffMaximal χ f) p volume ≤ C * eLpNorm f p volume) :
    MemLp (G.cutoffMaximalComplex_e2 χ f) p volume := by
  obtain ⟨x₀, hx₀⟩ := hf.norm.exists_forall_ge_of_hasCompactSupport hfc.norm
  refine ⟨(G.cutoffMaximalComplex_e2_measurable χ hχ hc hγ hf).aestronglyMeasurable, ?_⟩
  rw [G.cutoffMaximalComplex_e2_eLpNorm χ hχ hc hx₀]
  exact hb.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hfp.eLpNorm_lt_top)

/-- Any bound for the actual operator on compact continuous tests yields
an actual C-Lipschitz map on Lᵖ, with the same constant and norm bound. -/
theorem Family.exists_cutoffMaximal_Lp_extension_e2 {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (C : ℝ≥0)
    (hbound : ∀ f : Plane → ℂ, Continuous f → HasCompactSupport f → MemLp f p volume →
      eLpNorm (G.cutoffMaximal χ f) p volume ≤ C * eLpNorm f p volume) :
    ∃ T : Lp ℂ p (volume : Measure Plane) → Lp ℂ p (volume : Measure (Base 2)),
      LipschitzWith C T ∧ T 0 = 0 ∧ (∀ u, ‖T u‖ ≤ C * ‖u‖) ∧
      ∀ (f : Plane → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
        (hfp : MemLp f p volume),
        (T (hfp.toLp f) : Base 2 → ℂ) =ᵐ[volume] G.cutoffMaximalComplex_e2 χ f := by
  let R := compactContinuousLpTestRep_e2 (p := p)
  have hRcont (u : compactContinuousLpTests_e2 p) : Continuous (R u) :=
    (compactContinuousLpTestRep_e2_spec u).1
  have hRc (u : compactContinuousLpTests_e2 p) : HasCompactSupport (R u) :=
    (compactContinuousLpTestRep_e2_spec u).2.1
  have hRp (u : compactContinuousLpTests_e2 p) : MemLp (R u) p volume :=
    compactContinuousLpTestRep_e2_memLp u
  have hRT (u : compactContinuousLpTests_e2 p) :
      MemLp (G.cutoffMaximalComplex_e2 χ (R u)) p volume :=
    G.cutoffMaximalComplex_e2_memLp χ hχ hc hγ (hRcont u) (hRc u) (hRp u)
      (hbound (R u) (hRcont u) (hRc u) (hRp u))
  let F : compactContinuousLpTests_e2 p → Lp ℂ p (volume : Measure (Base 2)) :=
    fun u => (hRT u).toLp (G.cutoffMaximalComplex_e2 χ (R u))
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
      _ ≤ eLpNorm (G.cutoffMaximalComplex_e2 χ (R u - R v)) p volume := by
        apply eLpNorm_mono
        intro z
        exact G.cutoffMaximalComplex_e2_norm_sub_le χ hχ hc hγ (hRcont u) (hRcont v) hBu hBv z
      _ = eLpNorm (G.cutoffMaximal χ (R u - R v)) p volume :=
        G.cutoffMaximalComplex_e2_eLpNorm χ hχ hc hBd p
      _ ≤ C * eLpNorm (R u - R v) p volume :=
        hbound (R u - R v) ((hRcont u).sub (hRcont v)) ((hRc u).sub (hRc v)) ((hRp u).sub (hRp v))
      _ = _ := by rw [hinput]
  have hdense := compactContinuousLpTests_e2_dense p hp
  let T := hdense.extend F
  have hTlip : LipschitzWith C T := hdense.lipschitzWith_extend hFlip
  have hagree (f : Plane → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
      (hfp : MemLp f p volume) :
      (T (hfp.toLp f) : Base 2 → ℂ) =ᵐ[volume] G.cutoffMaximalComplex_e2 χ f := by
    let u : compactContinuousLpTests_e2 p := ⟨hfp.toLp f, f, hf, hfc, hfp, rfl⟩
    have hrepLp : (hRp u).toLp (R u) = hfp.toLp f := compactContinuousLpTestRep_e2_toLp u
    have hrep : R u = f := Measure.eq_of_ae_eq
      ((MemLp.toLp_eq_toLp_iff (hRp u) hfp).mp hrepLp) (hRcont u) hf
    have he : T (hfp.toLp f) = F u := hdense.extend_of_ind hFlip.uniformContinuous u
    rw [he]
    change ((hRT u).toLp (G.cutoffMaximalComplex_e2 χ (R u)) : Base 2 → ℂ) =ᵐ[volume] _
    simpa only [hrep] using (hRT u).coeFn_toLp
  have hTzero : T 0 = 0 := by
    have he := hagree 0 continuous_zero (by simpa using (HasCompactSupport.zero :
      HasCompactSupport (0 : Plane → ℂ))) (MemLp.zero (p := p))
    apply Lp.ext
    have he' : (T 0 : Base 2 → ℂ) =ᵐ[volume] 0 := by
      simpa only [MemLp.toLp_zero, G.cutoffMaximalComplex_e2_zero] using he
    exact he'.trans (Lp.coeFn_zero ℂ p (volume : Measure (Base 2))).symm
  refine ⟨T, hTlip, hTzero, ?_, hagree⟩
  intro u
  have hh := hTlip.dist_le_mul u 0
  simpa only [hTzero, dist_zero_right] using hh

/-- Agreement with the original operator on every compact continuous
test determines any continuous ambient Lᵖ extension uniquely. -/
theorem Family.cutoffMaximal_Lp_extension_unique_e2 {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {T S : Lp ℂ p (volume : Measure Plane) → Lp ℂ p (volume : Measure (Base 2))}
    (hT : Continuous T) (hS : Continuous S)
    (hTagree : ∀ (f : Plane → ℂ) (_hf : Continuous f) (_hc : HasCompactSupport f)
      (hfp : MemLp f p volume),
      (T (hfp.toLp f) : Base 2 → ℂ) =ᵐ[volume] G.cutoffMaximalComplex_e2 χ f)
    (hSagree : ∀ (f : Plane → ℂ) (_hf : Continuous f) (_hc : HasCompactSupport f)
      (hfp : MemLp f p volume),
      (S (hfp.toLp f) : Base 2 → ℂ) =ᵐ[volume] G.cutoffMaximalComplex_e2 χ f) : T = S := by
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
