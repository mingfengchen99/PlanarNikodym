import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! Summing actual Taylor fields up to a closed convex boundary. Uniform
summable bounds on every derivative imply a genuine C∞ Taylor field on
the closed set, via differentiability on its interior and the boundary
derivative extension theorem. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace PlanarNikodym
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem e2_hasFTaylorSeries_tsum_closed_convex {ι : Type*}
    {s : Set E} (hs : Convex ℝ s) (hclosure : closure (interior s) = s)
    (f : ι → E → F) (p : ι → E → FormalMultilinearSeries ℝ E F)
    (hp : ∀ i, HasFTaylorSeriesUpToOn ∞ (f i) (p i) s)
    (v : ℕ → ι → ℝ) (hv : ∀ m, Summable (v m))
    (hb : ∀ m i x, x ∈ s → ‖p i x m‖ ≤ v m i) :
    HasFTaylorSeriesUpToOn ∞ (fun x => ∑' i, f i x)
      (fun x m => ∑' i, p i x m) s := by
  let P : E → FormalMultilinearSeries ℝ E F := fun x m => ∑' i, p i x m
  have hmle (m : ℕ) : (m : ℕ∞ω) ≤ ∞ := by
    exact_mod_cast (show (m : ℕ∞) ≤ ⊤ from le_top)
  have hmlt (m : ℕ) : (m : ℕ∞ω) < ∞ := by
    exact_mod_cast (show (m : ℕ∞) < ⊤ from WithTop.coe_lt_top m)
  have hsum (m : ℕ) (x : E) (hx : x ∈ s) : Summable (fun i => p i x m) :=
    (hv m).of_norm_bounded (fun i => hb m i x hx)
  have hcont (m : ℕ) : ContinuousOn (fun x => P x m) s :=
    continuousOn_tsum (fun i => (hp i).cont m (hmle m)) (hv m) (fun i x hx => hb m i x hx)
  have hcurry (m : ℕ) (x : E) (hx : x ∈ s) :
      (P x (m + 1)).curryLeft = ∑' i, (p i x (m + 1)).curryLeft := by
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) F).toContinuousLinearEquiv.toContinuousLinearMap.map_tsum
      (hsum (m + 1) x hx)
  have hder (m : ℕ) (x : E) (hx : x ∈ interior s) :
      HasFDerivAt (fun x => P x m) (P x (m + 1)).curryLeft x := by
    have hd (i : ι) (y : E) (hy : y ∈ interior s) :
        HasFDerivAt (fun x => p i x m) (p i y (m + 1)).curryLeft y :=
      ((hp i).fderivWithin m (hmlt m) y (interior_subset hy)).hasFDerivAt
        (mem_of_superset (isOpen_interior.mem_nhds hy) interior_subset)
    have hbd (i : ι) (y : E) (hy : y ∈ interior s) :
        ‖(p i y (m + 1)).curryLeft‖ ≤ v (m + 1) i := by
      simpa only [ContinuousMultilinearMap.curryLeft_norm] using hb (m + 1) i y (interior_subset hy)
    have hh := hasFDerivAt_tsum_of_isPreconnected (hv (m + 1)) isOpen_interior
      hs.interior.isPreconnected hd hbd hx (hsum m x (interior_subset hx)) hx
    rw [← hcurry m x (interior_subset hx)] at hh
    exact hh
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hh := (continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv.toContinuousLinearMap.map_tsum (hsum 0 x hx)
    change (∑' i, p i x 0).curry0 = ∑' i, f i x
    calc
      _ = ∑' i, (p i x 0).curry0 := hh
      _ = _ := tsum_congr (fun i => (hp i).zero_eq x hx)
  · intro m _ x hx
    have hc : ∀ y ∈ closure (interior s), ContinuousWithinAt (fun z => P z m) (interior s) y := by
      intro y hy
      rw [hclosure] at hy
      exact (hcont m y hy).mono interior_subset
    have ht : Tendsto (fun y => (P y (m + 1)).curryLeft) (𝓝[interior s] x)
        (𝓝 (P x (m + 1)).curryLeft) :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) F).continuous.continuousAt.tendsto.comp
        ((hcont (m + 1) x hx).mono interior_subset)
    have he : (fun y => fderiv ℝ (fun z => P z m) y) =ᶠ[𝓝[interior s] x]
        (fun y => (P y (m + 1)).curryLeft) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hder m y hy).fderiv
    have hh := hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun y hy => (hder m y hy).differentiableAt.differentiableWithinAt)
      hs.interior isOpen_interior hc (ht.congr' he.symm)
    simpa only [hclosure] using hh
  · intro m _
    exact hcont m

end PlanarNikodym
