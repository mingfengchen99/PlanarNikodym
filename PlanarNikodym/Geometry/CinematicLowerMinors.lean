import PlanarNikodym.Geometry.CinematicJetCoordinates
import PlanarNikodym.Rank.InitialMatrixMinors
import PlanarNikodym.Analysis.Localization.FiniteCutoffPartition
import PlanarNikodym.Analysis.Maximal.Averaging

/-! Coordinate minors for every lower time-jet degree are selected from
the actual cinematic matrix, then retained on actual smooth local pieces. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace PlanarNikodym

def Family.cinematicInitialMinor {d m : ℕ} (G : Family 2 d) (hm : m ≤ d + 2)
    (σ : Fin m ↪ Fin (d + 2)) (x : ℝ × Parameters 2 d) : ℝ :=
  Matrix.det (fun i j : Fin m => G.cinematicMatrix x (Fin.castLE hm i) (σ j))

theorem Family.exists_cinematicInitialMinor {d : ℕ} (G : Family 2 d)
    {x : ℝ × Parameters 2 d} (hdet : G.cinematicDet x ≠ 0) (m : ℕ) (hm : m ≤ d + 2) :
    ∃ σ : Fin m ↪ Fin (d + 2), G.cinematicInitialMinor hm σ x ≠ 0 :=
  exists_initial_coordinate_minor (G.cinematicMatrix x) hdet hm

theorem Family.cinematicInitialMinor_analyticAt {d m : ℕ} (G : Family 2 d)
    (hm : m ≤ d + 2) (σ : Fin m ↪ Fin (d + 2)) {x : ℝ × Parameters 2 d}
    (ha : AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x) :
    AnalyticAt ℝ (G.cinematicInitialMinor hm σ) x := by
  apply analyticAt_det
  intro i j
  exact timeDerivative_analyticAt (G.parameterColumn_analyticAt ha (σ j)) (Fin.castLE hm i)

/-- The selected actual coordinate minor is bounded away from zero on
an open analytic neighborhood of the original point. -/
theorem Family.exists_cinematicInitialMinor_patch {d : ℕ} (G : Family 2 d)
    {x : ℝ × Parameters 2 d}
    (ha : AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    (hdet : G.cinematicDet x ≠ 0) (m : ℕ) (hm : m ≤ d + 2) :
    ∃ (σ : Fin m ↪ Fin (d + 2)) (U : Set (ℝ × Parameters 2 d)) (b : ℝ),
      IsOpen U ∧ x ∈ U ∧ 0 < b ∧ ∀ y ∈ U,
        AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) y ∧
          b ≤ |G.cinematicInitialMinor hm σ y| := by
  obtain ⟨σ, hσ⟩ := G.exists_cinematicInitialMinor hdet m hm
  let b : ℝ := |G.cinematicInitialMinor hm σ x| / 2
  have habs : 0 < |G.cinematicInitialMinor hm σ x| := abs_pos.mpr hσ
  have hb : 0 < b := half_pos habs
  have hlt : b < |G.cinematicInitialMinor hm σ x| := by dsimp [b]; linarith
  have he : ∀ᶠ y in 𝓝 x,
      AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) y ∧
        b < |G.cinematicInitialMinor hm σ y| :=
    ha.eventually_analyticAt.and
      ((G.cinematicInitialMinor_analyticAt hm σ ha).continuousAt.abs.preimage_mem_nhds
        (Ioi_mem_nhds hlt))
  obtain ⟨U, hU, hUo, hxU⟩ := mem_nhds_iff.mp he
  exact ⟨σ, U, b, hUo, hxU, hb, fun y hy => ⟨(hU hy).1, (hU hy).2.le⟩⟩

/-- A compact cinematic cutoff splits into finitely many actual smooth
cutoffs, each with its own explicitly selected lower coordinate minor
and a positive minor bound on its entire closed support. -/
theorem Family.exists_finite_cinematicInitialMinor_cutoff_partition
    {d : ℕ} (G : Family 2 d) (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (ha : ∀ x ∈ tsupport χ,
      AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    (hdet : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0) (m : ℕ) (hm : m ≤ d + 2) :
    ∃ (S : Finset (tsupport χ)) (ψ : S → Cutoff d)
      (σ : S → (Fin m ↪ Fin (d + 2))) (b : S → ℝ),
      (∀ i, ContDiff ℝ ∞ (ψ i) ∧ HasCompactSupport (ψ i) ∧
        tsupport (ψ i) ⊆ tsupport χ ∧ 0 < b i ∧
        (∀ x ∈ tsupport (ψ i),
          AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x ∧
            b i ≤ |G.cinematicInitialMinor hm (σ i) x|) ∧
        ∀ x, 0 ≤ ψ i x ∧ ψ i x ≤ χ x) ∧
      ∀ x, ∑ i : S, ψ i x = χ x := by
  classical
  have hpatch (q : tsupport χ) :=
    G.exists_cinematicInitialMinor_patch (ha q q.property) (hdet q q.property) m hm
  choose σ U b hU hqU hb hgood using hpatch
  have hcover : tsupport χ ⊆ ⋃ q : tsupport χ, U q := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hqU ⟨x, hx⟩⟩
  obtain ⟨S, ψ, hψ, hsum⟩ := exists_finite_cutoff_partition χ hχ hc hχ0 U hU hcover
  refine ⟨S, ψ, (fun i => σ i.val), (fun i => b i.val), ?_, hsum⟩
  intro i
  obtain ⟨hi, hci, hsχ, hsU, hr⟩ := hψ i
  exact ⟨hi, hci, hsχ, hb i.val, fun x hx => hgood i.val x (hsU hx), hr⟩

end PlanarNikodym
