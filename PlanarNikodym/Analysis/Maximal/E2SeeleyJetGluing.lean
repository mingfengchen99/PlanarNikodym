import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Piecewise

/-! Pasting actual Taylor fields across a closed cover. In the Seeley
application these are the two closed half spaces; equality of all boundary
jets supplies actual ambient C∞ regularity, not just one-sided smoothness. -/
noncomputable section
open Set
open scoped ContDiff
namespace PlanarNikodym
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem e2_hasFTaylorSeries_piecewise_closed
    {s t : Set E} [DecidablePred (· ∈ s)] (hs : IsClosed s) (ht : IsClosed t) (hst : s ∪ t = univ)
    {n : ℕ∞ω} {f g : E → F} {p q : E → FormalMultilinearSeries ℝ E F}
    (hp : HasFTaylorSeriesUpToOn n f p s) (hq : HasFTaylorSeriesUpToOn n g q t)
    (hjet : ∀ x ∈ s ∩ t, p x = q x) :
    HasFTaylorSeriesUpToOn n (s.piecewise f g) (s.piecewise p q) univ := by
  classical
  let P := s.piecewise p q
  have hPs (m : ℕ) : EqOn (fun x => P x m) (fun x => p x m) s := by
    intro x hx
    simp [P, hx]
  have hPt (m : ℕ) : EqOn (fun x => P x m) (fun x => q x m) t := by
    intro x hx
    by_cases hxs : x ∈ s
    · simp [P, hxs, hjet x ⟨hxs, hx⟩]
    · simp [P, hxs]
  refine ⟨?_, ?_, ?_⟩
  · intro x _
    by_cases hx : x ∈ s
    · simpa [hx] using hp.zero_eq x hx
    · have hxt : x ∈ t := by
        have hh : x ∈ s ∪ t := hst ▸ mem_univ x
        exact hh.resolve_left hx
      simpa [hx] using hq.zero_eq x hxt
  · intro m hm x _
    have hdS : HasFDerivWithinAt (fun x => P x m) (P x (m + 1)).curryLeft s x := by
      by_cases hx : x ∈ s
      · have hh := (hp.fderivWithin m hm x hx).congr' (hPs m) hx
        simpa [P, hx] using hh
      · exact HasFDerivWithinAt.of_notMem_closure (by rwa [hs.closure_eq])
    have hdT : HasFDerivWithinAt (fun x => P x m) (P x (m + 1)).curryLeft t x := by
      by_cases hx : x ∈ t
      · have hh := (hq.fderivWithin m hm x hx).congr' (hPt m) hx
        have he := congrArg (fun r : FormalMultilinearSeries ℝ E F => (r (m + 1)).curryLeft)
          (show P x = q x from funext fun j => hPt j hx)
        rw [he]
        exact hh
      · exact HasFDerivWithinAt.of_notMem_closure (by rwa [ht.closure_eq])
    simpa only [hst] using hdS.union hdT
  · intro m hm
    have hcS := (hp.cont m hm).congr (hPs m)
    have hcT := (hq.cont m hm).congr (hPt m)
    simpa only [hst] using hcS.union_of_isClosed hcT hs ht

theorem e2_contDiff_piecewise_of_matching_closed_jets
    {s t : Set E} [DecidablePred (· ∈ s)] (hs : IsClosed s) (ht : IsClosed t) (hst : s ∪ t = univ)
    {f g : E → F} {p q : E → FormalMultilinearSeries ℝ E F}
    (hp : HasFTaylorSeriesUpToOn ∞ f p s) (hq : HasFTaylorSeriesUpToOn ∞ g q t)
    (hjet : ∀ x ∈ s ∩ t, p x = q x) : ContDiff ℝ ∞ (s.piecewise f g) := by
  classical
  have hh := e2_hasFTaylorSeries_piecewise_closed hs ht hst hp hq hjet
  exact contDiffOn_univ.mp hh.contDiffOn

end PlanarNikodym
