import PlanarNikodym.Reduction.CenterReduction
import PlanarNikodym.Examples.Examples

noncomputable section
open Set Submodule Module
namespace PlanarNikodym.Examples

/-- Two completely unused auxiliary parameters exercise m=0 in Corollary 6.2. -/
abbrev constantFamily (I : Interval) : Family 2 2 := ⟨I, univ, fun _ _ => 0⟩

theorem constantFamily_ranks (I : Interval) (p : Parameters 2 2) :
    (constantFamily I).pointRank p = 0 ∧ (constantFamily I).curveRank p = 0 := by
  have hu : (constantFamily I).uColumn p = 0 := by
    funext i t
    change fderiv ℝ (fun _ : Aux 2 => (0 : ℝ)) p.2 (Pi.single i 1) = 0
    simp
  have hz : (constantFamily I).zColumn p = 0 := by
    funext i t
    change fderiv ℝ (fun _ : Base 2 => (0 : ℝ)) p.1 (Pi.single i 1) = 0
    simp
  have hu' : (constantFamily I).pointSpace p = ⊥ := by
    change span ℝ (range ((constantFamily I).uColumn p)) = ⊥
    rw [hu]
    simp
  have hz' : span ℝ (range ((constantFamily I).zColumn p)) = ⊥ := by
    rw [hz]
    simp
  constructor
  · change finrank ℝ ((constantFamily I).pointSpace p) = 0
    rw [hu']
    simp
  · change finrank ℝ ((constantFamily I).pointSpace p ⊔
      span ℝ (range ((constantFamily I).zColumn p)) : Submodule ℝ (I.carrier → ℝ)) = 0
    rw [hu', hz']
    simp

theorem constantFamily_reduction (I : Interval) (q : Parameters 2 2) :
    ∃ U : Set (Parameters 2 2), IsOpen U ∧ q ∈ U ∧
    ∃ G' : Family 2 0, G'.IsAnalytic ∧
      (∀ p ∈ G'.W, G'.pointRank p = 0 ∧ G'.curveRank p = 0) ∧
      ∀ z, (constantFamily I).curvesAtOn U z = G'.curvesAtOn G'.W z := by
  have ha : (constantFamily I).IsAnalytic := by
    intro p hp
    exact analyticAt_const
  obtain ⟨U, hU, hq, _, Wz, Wu, G', _, _, _, _, _, _, hga, hgr, he⟩ :=
    corollary_6_2 (constantFamily I) isOpen_univ ha
      (fun p _ => (constantFamily_ranks I p).1)
      (fun p _ => (constantFamily_ranks I p).2) q (mem_univ q)
  exact ⟨U, hU, hq, G', hga, hgr, he⟩

theorem lines_analytic (I : Interval) : (lines I).IsAnalytic := by
  intro p hp
  change AnalyticAt ℝ (fun x : ℝ × Parameters 2 1 =>
    x.2.1 1 + x.2.2 0 * (x.1 - x.2.1 0)) p
  have hz : AnalyticAt ℝ (fun x : ℝ × Parameters 2 1 => x.2.1) p :=
    analyticAt_fst.comp analyticAt_snd
  have hu : AnalyticAt ℝ (fun x : ℝ × Parameters 2 1 => x.2.2) p :=
    analyticAt_snd.comp analyticAt_snd
  have hzi (i : Fin 2) : AnalyticAt ℝ (fun x : ℝ × Parameters 2 1 => x.2.1 i) p :=
    ((ContinuousLinearMap.proj i : Base 2 →L[ℝ] ℝ).analyticAt _).comp hz
  have hui : AnalyticAt ℝ (fun x : ℝ × Parameters 2 1 => x.2.2 0) p :=
    ((ContinuousLinearMap.proj 0 : Aux 1 →L[ℝ] ℝ).analyticAt _).comp hu
  exact (hzi 1).add (hui.mul (analyticAt_fst.sub (hzi 0)))

/-- The line family has point rank 1 and curve rank 2, so Corollary 6.3
produces a local analytic reparametrization freezing one centre coordinate. -/
theorem lines_center_reduction (I : Interval) (q : Parameters 2 1) :
    ∃ j : Fin 2, ∃ E : OpenPartialHomeomorph (Parameters 2 1) (Parameters 2 1),
      q ∈ E.source ∧ AnalyticOnNhd ℝ E E.source ∧
      AnalyticOnNhd ℝ E.symm E.target ∧
      (∀ p ∈ E.source, p.1 j.rev = q.1 j.rev → E p = p) ∧
      ∀ p ∈ E.source, ∀ t ∈ I.carrier,
        (lines I).γ t (E p) = (lines I).γ t (centerSlice j q p) := by
  obtain ⟨j, E, hq, _, _, hea, heia, _, hn, he⟩ :=
    corollary_6_3 (lines I) isOpen_univ (lines_analytic I)
      (fun p _ => (lines_ranks I p).1)
      (fun p _ => (lines_ranks I p).2) q (mem_univ q)
  exact ⟨j, E, hq, hea, heia, hn, he⟩

end PlanarNikodym.Examples
