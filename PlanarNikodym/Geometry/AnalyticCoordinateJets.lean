import PlanarNikodym.Geometry.LocalCoordinates
import PlanarNikodym.Core.Definitions
import Mathlib.LinearAlgebra.Multilinear.Pi

/-! Actual finite coordinate jets and analytic nonflatness. The order of
the first nonzero derivative is not an additional assumption. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology

namespace PlanarNikodym

def coordinateJet {n : ℕ} (f : Base n → ℝ) (k : ℕ) (s : Fin k → Fin n)
    (x : Base n) : ℝ :=
  iteratedFDeriv ℝ k f x (fun i => Pi.single (s i) 1)

@[simp] theorem coordinateJet_zero {n : ℕ} (f : Base n → ℝ)
    (s : Fin 0 → Fin n) (x : Base n) : coordinateJet f 0 s x = f x := rfl

theorem coordinateJet_analytic {n : ℕ} {f : Base n → ℝ} {W : Set (Base n)}
    (ha : AnalyticOnNhd ℝ f W) (k : ℕ) (s : Fin k → Fin n) :
    AnalyticOnNhd ℝ (coordinateJet f k s) W := by
  let A := ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Base n) ℝ
    (fun i => Pi.single (s i) 1)
  exact fun x hx => (A.analyticAt _).comp (f := iteratedFDeriv ℝ k f)
    (ha.iteratedFDeriv k x hx)

theorem coordinateJet_cons {n k : ℕ} {f : Base n → ℝ} {W : Set (Base n)}
    (ha : AnalyticOnNhd ℝ f W) (s : Fin k → Fin n) (j : Fin n)
    {x : Base n} (hx : x ∈ W) :
    coordinateJet f (k + 1) (Fin.cons j s) x =
      fderiv ℝ (coordinateJet f k s) x (Pi.single j 1) := by
  let A := ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Base n) ℝ
    (fun i => Pi.single (s i) 1)
  change _ = fderiv ℝ (A ∘ iteratedFDeriv ℝ k f) x (Pi.single j 1)
  rw [fderiv_comp x A.differentiableAt (ha.iteratedFDeriv k x hx).differentiableAt,
    A.hasFDerivAt.fderiv]
  rfl

/-- Coordinate evaluations detect a multilinear map, even when either
the derivative order or the coordinate dimension is zero. -/
theorem multilinear_eq_zero_of_coordinate_values {n k : ℕ}
    (L : (Base n) [×k]→L[ℝ] ℝ)
    (h : ∀ s : Fin k → Fin n, L (fun i => Pi.single (s i) 1) = 0) : L = 0 := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply MultilinearMap.pi_ext
  intro s
  apply MultilinearMap.ext_ring
  exact h s

/-- A flat analytic germ is zero on a neighbourhood. The proof uses
the convergent Taylor series, not formal-series uniqueness alone. -/
theorem analytic_eventually_zero_of_coordinateJets_zero {n : ℕ}
    {f : Base n → ℝ} {x : Base n} (ha : AnalyticAt ℝ f x)
    (hzero : ∀ k (s : Fin k → Fin n), coordinateJet f k s x = 0) :
    ∀ᶠ y in 𝓝 x, f y = 0 := by
  have hder (k : ℕ) : iteratedFDeriv ℝ k f x = 0 :=
    multilinear_eq_zero_of_coordinate_values _ (hzero k)
  obtain ⟨P, r, hP⟩ := ha
  filter_upwards [Metric.eball_mem_nhds x hP.r_pos] with y hy
  have hy' : y - x ∈ Metric.eball (0 : Base n) r := by
    simpa only [Metric.mem_eball, edist_eq_enorm_sub, sub_zero] using hy
  have hs := hP.hasSum_iteratedFDeriv hy'
  have hs' : HasSum (fun _ : ℕ => (0 : ℝ)) (f y) := by
    simpa only [hder, ContinuousMultilinearMap.zero_apply, smul_zero,
      add_sub_cancel] using hs
  exact hs'.unique hasSum_zero

end PlanarNikodym
