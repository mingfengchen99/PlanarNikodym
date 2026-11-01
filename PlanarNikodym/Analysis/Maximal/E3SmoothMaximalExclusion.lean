import PlanarNikodym.Analysis.Jets.E3SmoothJetSmoothing
import PlanarNikodym.Analysis.Maximal.E3ZeroDimSmoothExclusion

/-! Corollary 1.2 for the original generally smooth closed-interval
family. Compact interior replacements, genuine C∞ estimates, and the
zero-dimensional Fubini argument remove every analytic premise. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff NNReal
namespace PlanarNikodym

theorem Family.exists_e3_cinematic_cutoff_neighborhood {d : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (hd : ∀ t ∈ G.I.carrier, ∀ p ∈ G.W, G.cinematicDet (t, p) ≠ 0)
    (q : Parameters 2 d) (hq : q ∈ G.W) :
    ∃ (U : Set (Parameters 2 d)) (χ : Cutoff d),
      IsOpen U ∧ q ∈ U ∧ U ⊆ G.W ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ t ∈ G.I.carrier, ∀ p ∈ U, χ (t, p) = 1) ∧
      (∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0) := by
  let K : Set (ℝ × Parameters 2 d) := G.I.carrier ×ˢ {q}
  let S : Set (ℝ × Parameters 2 d) := {x | G.cinematicDet x ≠ 0}
  have hK : IsCompact K := isCompact_Icc.prod isCompact_singleton
  have hS : IsOpen S := (G.continuous_cinematicDet_of_contDiff hG).isOpen_preimage _
    isClosed_singleton.isOpen_compl
  have hKS : K ⊆ S := by
    rintro ⟨t, p⟩ ⟨ht, hp⟩
    have hpq : p = q := hp
    subst p
    exact hd t ht q hq
  obtain ⟨χ, N, hχ, hc, hχr, hN, hKN, hN1, hχS⟩ :=
    exists_compact_smooth_cutoff hK hS hKS
  obtain ⟨T, U, _, hU, hIT, hqU, hTU⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hN hKN
  refine ⟨U ∩ G.W, χ, hU.inter hW, ⟨hqU (mem_singleton q), hq⟩,
    inter_subset_right, hχ, hc, hχr, ?_, hχS⟩
  intro t ht p hp
  exact hN1 (t, p) (hTU ⟨hIT ht, hp.1⟩)

/-- All fields of the actual smooth maximal package are constructed from
the C∞ cinematic hypothesis in positive auxiliary dimension. -/
theorem Family.exists_e3_smooth_maximal_package {d : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) (hdim : 1 ≤ d)
    (hd : ∀ t ∈ G.I.carrier, ∀ p ∈ G.W, G.cinematicDet (t, p) ≠ 0)
    (q : Parameters 2 d) (hq : q ∈ G.W) :
    ∃ U : Set (Parameters 2 d), IsOpen U ∧ q ∈ U ∧ U ⊆ G.W ∧
      Nonempty (SmoothMaximalPackage G U) := by
  obtain ⟨U, χ, hU, hqU, hUW, hχ, hc, hr, hχ1, hdet⟩ :=
    G.exists_e3_cinematic_cutoff_neighborhood hW hG hd q hq
  let L := standardFrequencyCutoff
  let p := smoothingThreshold d
  let ε : ℝ := 1 / (4 * (p : ℝ))
  have hp1 : (1 : ℝ≥0) ≤ p := smoothingThreshold_one_le d
  have hpR : 0 < (p : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hp1)
  have hε0 : 0 < ε := by dsimp [ε]; positivity
  have hε : ε < 1 / (p : ℝ) := by
    dsimp [ε]
    exact one_div_lt_one_div_of_lt hpR (by nlinarith)
  have hS : JetSmoothingInput G χ L p (d + 1) ε :=
    G.e3_jetSmoothingInput_of_cinematic_support hG hdim χ hχ hc
      (fun x => (hr x).1) hdet L p le_rfl (d + 1) hε0
  refine ⟨U, hU, hqU, hUW, ⟨?_⟩⟩
  exact smoothMaximalPackage_aux G U χ L hχ hc (fun _ _ => hG.contDiffAt)
    (fun x => (hr x).1) (fun t ht r hr => (hχ1 t ht r hr).symm.le)
    p le_rfl ε hε0 hε (Nat.le_succ d) (Nat.succ_pos d) hS

theorem Family.e3_timeIncidence_null_of_contDiff {d : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) (hdim : 1 ≤ d)
    (hd : ∀ t ∈ G.I.carrier, ∀ p ∈ G.W, G.cinematicDet (t, p) ≠ 0)
    (E : Set Plane) (hE : MeasurableSet E) (hE0 : volume E = 0) :
    volume (G.timeIncidenceCenters G.W E) = 0 := by
  rw [G.timeIncidenceCenters_eq hG.contDiffOn G.W Subset.rfl E]
  apply G.incidence_null_of_local ?_ E hE hE0
  intro q hq
  obtain ⟨U, hU, hqU, hUW, ⟨D⟩⟩ := G.exists_e3_smooth_maximal_package hW hG hdim hd q hq
  refine ⟨U, hU, hqU, ?_⟩
  intro F hF hF0
  rw [← G.timeIncidenceCenters_eq hG.contDiffOn U hUW F]
  exact (D.open_maximal_estimate hU hUW hG.contDiffOn).incidence_null
    hUW hG.contDiffOn F hF hF0

/-- The complete outer-null form of Corollary 1.2. Smoothness is assumed
only on the original closed time interval times the open parameter set. -/
theorem Family.e3_timeIncidence_null_of_isSmooth {d : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W) (hG : G.IsSmooth)
    (hd : ∀ t ∈ G.I.carrier, ∀ p ∈ G.W, G.cinematicDet (t, p) ≠ 0)
    (E : Set Plane) (hE : MeasurableSet E) (hE0 : volume E = 0) :
    volume (G.timeIncidenceCenters G.W E) = 0 := by
  rcases d with _ | d
  · exact G.e3_zero_dim_timeIncidence_null_of_isSmooth hW hG hd E hE hE0
  apply G.timeIncidenceCenters_null_of_interiorIntervals G.W E
  intro i
  let J := interiorInterval G.I i
  have hJ : J.carrier ⊆ G.I.carrier :=
    (interiorInterval_subset G.I i).trans Ioo_subset_Icc_self
  have hGs : (G.withInterval J).IsSmooth := hG.mono (prod_mono hJ Subset.rfl)
  rw [(G.withInterval J).timeIncidenceCenters_eq hGs G.W Subset.rfl E]
  apply (G.withInterval J).incidence_null_of_local ?_ E hE hE0
  intro q hq
  obtain ⟨U, H, hU, hqU, hUW, hI, hHW, hH, heq, hdet⟩ :=
    G.exists_e3_interior_smooth_extension hW hG i q hq
  refine ⟨U, hU, hqU, ?_⟩
  intro F hF hF0
  have hHd : ∀ t ∈ H.I.carrier, ∀ p ∈ H.W, H.cinematicDet (t, p) ≠ 0 := by
    intro t ht p hp
    have htJ : t ∈ J.carrier := by simpa only [hI] using ht
    have hpU : p ∈ U := hHW ▸ hp
    rw [hdet (t, p) ⟨htJ, hpU⟩]
    exact hd t (hJ htJ) p (hUW hpU)
  have hnullH := H.e3_timeIncidence_null_of_contDiff (hHW.symm ▸ hU)
    hH (Nat.succ_le_succ (Nat.zero_le d)) hHd F hF hF0
  rw [H.timeIncidenceCenters_eq hH.contDiffOn H.W Subset.rfl F] at hnullH
  apply measure_mono_null (t := H.incidenceCenters H.W F) ?_ hnullH
  rintro z ⟨u, hu, hz⟩
  refine ⟨u, hHW.symm ▸ hu, ?_⟩
  have hcurve : (G.withInterval J).curve (z, u) = H.curve (z, u) := by
    change (fun t => (t, G.γ t (z, u))) '' J.carrier =
      (fun t => (t, H.γ t (z, u))) '' H.I.carrier
    rw [hI]
    apply Set.image_congr
    intro t ht
    exact Prod.ext rfl (heq t ht (z, u) hu).symm
  rwa [← hcurve]

theorem corollary_1_2_smooth {d : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W) (hG : G.IsSmooth)
    (hd : ∀ t ∈ G.I.carrier, ∀ p ∈ G.W, G.cinematicDet (t, p) ≠ 0) :
    ¬ G.AdmitsNikodym := by
  apply G.no_nikodym_of_incidence_null
  intro E hE hE0
  rw [← G.timeIncidenceCenters_eq hG G.W Subset.rfl E]
  exact G.e3_timeIncidence_null_of_isSmooth hW hG hd E hE hE0

end PlanarNikodym
