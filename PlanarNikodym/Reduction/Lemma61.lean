import PlanarNikodym.Geometry.BlockGeometry

noncomputable section
open Set Filter Submodule Module Metric
open scoped Topology
namespace PlanarNikodym

/-- The two ranks in (6.1), written using actual partial derivatives
and functions on the specified time set. -/
def PartialBlockRank {a b c : ℕ} (I : Set ℝ)
    (φ : ℝ → BlockParameters a b c → ℝ) (p : BlockParameters a b c) : Prop :=
  let fw : Fin b → I → ℝ := fun j t =>
    fderiv ℝ (fun w => φ t ((p.1.1, w), p.2)) p.1.2 (Pi.single j 1)
  let fη : Fin c → I → ℝ := fun j t =>
    fderiv ℝ (fun η => φ t (p.1, η)) p.2 (Pi.single j 1)
  finrank ℝ (span ℝ (range fw)) = b ∧
    finrank ℝ (span ℝ (range fw) ⊔ span ℝ (range fη) : Submodule ℝ (I → ℝ)) = b

theorem blockRank_iff_partial {a b c : ℕ} (I : Set ℝ)
    (φ : ℝ → BlockParameters a b c → ℝ) (p : BlockParameters a b c)
    (hf : ∀ t : I, DifferentiableAt ℝ (φ t) p) :
    BlockRank (fun (t : I) => φ t) p ↔ PartialBlockRank I φ p := by
  have hw := wDerivative_eq_slice (fun (t : I) => φ t) p hf
  have hη : etaDerivative (fun (t : I) => φ t) p =
      functionDerivative (fun (t : I) η => φ t (p.1, η)) p.2 := by
    rw [functionDerivative_snd_slice _ p hf]
    rfl
  unfold BlockRank
  rw [hw, hη, range_eq_span_coordinates, range_eq_span_coordinates]
  rfl

/-- Lemma 6.1 with the paper's joint analyticity and partial-derivative ranks.
Taking I to be a closed interval gives the paper's exact time domain. -/
theorem lemma_6_1_interval {a b c : ℕ} (I : Set ℝ)
    (φ : ℝ → BlockParameters a b c → ℝ) (W : Set (BlockParameters a b c))
    (hW : IsOpen W) (q : BlockParameters a b c) (hq : q ∈ W)
    (hf : AnalyticOnNhd ℝ (fun tp : ℝ × BlockParameters a b c => φ tp.1 tp.2) (I ×ˢ W))
    (hr : ∀ p ∈ W, PartialBlockRank I φ p) :
    ∃ r : ℝ, 0 < r ∧ ∃ κ : BlockParameters a b c → Aux b,
    ∃ e : OpenPartialHomeomorph (BlockParameters a b c) (BlockParameters a b c),
      e.source = ball q r ∧ e.source ⊆ W ∧ e.target ⊆ W ∧
      (∀ p, e p = ((p.1.1, κ p), p.2)) ∧
      AnalyticOnNhd ℝ κ e.source ∧ AnalyticOnNhd ℝ e e.source ∧
      AnalyticOnNhd ℝ e.symm e.target ∧
      (∀ p ∈ e.source, p.2 = q.2 → κ p = p.1.2) ∧
      ∀ p ∈ e.source, ∀ t ∈ I, φ t (e p) = φ t (p.1, q.2) := by
  have hφ : ∀ t : I, AnalyticOnNhd ℝ (φ t) W := by
    intro t p hp
    exact (hf (t, p) ⟨t.property, hp⟩).comp (analyticAt_const.prod analyticAt_id)
  obtain ⟨r, hr₀, e, hes, hesW, hetW, _, hea, heia, hecoord, henorm, heid⟩ :=
    lemma_6_1 (fun (t : I) => φ t) W hW q hq hφ
      (fun p hp => (blockRank_iff_partial I φ p
        (fun t => (hφ t p hp).differentiableAt)).mpr (hr p hp))
  refine ⟨r, hr₀, fun p => (e p).1.2, e, hes, hesW, hetW, ?_, ?_, hea, heia, ?_, ?_⟩
  · intro p
    exact Prod.ext (Prod.ext (hecoord p).1 rfl) (hecoord p).2
  · intro p hp
    exact analyticAt_snd.comp (analyticAt_fst.comp (hea p hp))
  · intro p hp hη
    exact congrArg (fun x => x.1.2) (henorm p hp hη)
  · intro p hp t ht
    exact heid p hp ⟨t, ht⟩

end PlanarNikodym
