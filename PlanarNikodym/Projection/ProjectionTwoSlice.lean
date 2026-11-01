import PlanarNikodym.Projection.ProjectionStationarity
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Actual two-parameter slices of the scalar normal form.

The unused coordinates are held at the model's base point. The first
slice coordinate is the normalized centre coordinate, and the second is
any distinct parameter coordinate. -/

noncomputable section
open Set Filter Metric
open scoped Topology
namespace PlanarNikodym

def twoParameterInsert {d : ℕ} (w : Aux (d + 1)) (j : Fin (d + 1))
    (q : Plane) : Aux (d + 1) :=
  w + Pi.single 0 (q.1 - w 0) + Pi.single j (q.2 - w j)

@[simp] theorem twoParameterInsert_base {d : ℕ} (w : Aux (d + 1))
    (j : Fin (d + 1)) : twoParameterInsert w j (w 0, w j) = w := by
  simp [twoParameterInsert]

@[simp] theorem twoParameterInsert_head {d : ℕ} (w : Aux (d + 1))
    (j : Fin (d + 1)) (hj : j ≠ 0) (q : Plane) :
    twoParameterInsert w j q 0 = q.1 := by
  simp [twoParameterInsert, hj.symm]

theorem twoParameterInsert_analytic {d : ℕ} (w : Aux (d + 1))
    (j : Fin (d + 1)) : AnalyticOnNhd ℝ (twoParameterInsert w j) univ := by
  intro q _
  apply AnalyticAt.pi
  intro i
  simp only [twoParameterInsert, Pi.add_apply, Pi.single_apply]
  split_ifs
  · exact (analyticAt_const.add (analyticAt_fst.sub analyticAt_const)).add
      (analyticAt_snd.sub analyticAt_const)
  · exact (analyticAt_const.add (analyticAt_fst.sub analyticAt_const)).add analyticAt_const
  · exact (analyticAt_const.add analyticAt_const).add (analyticAt_snd.sub analyticAt_const)
  · exact analyticAt_const

theorem hasDerivAt_twoParameterInsert_head {d : ℕ} (w : Aux (d + 1))
    (j : Fin (d + 1)) (q : Plane) :
    HasDerivAt (fun y => twoParameterInsert w j (y, q.2)) (Pi.single 0 1) q.1 := by
  apply hasDerivAt_pi.mpr
  intro i
  simp only [twoParameterInsert, Pi.add_apply, Pi.single_apply]
  split_ifs
  · simpa using ((hasDerivAt_const q.1 (w i)).add
      ((hasDerivAt_id q.1).sub_const (w 0))).add_const (q.2 - w j)
  · simpa using ((hasDerivAt_const q.1 (w i)).add
      ((hasDerivAt_id q.1).sub_const (w 0))).add_const 0
  · exact hasDerivAt_const q.1 (w i + 0 + (q.2 - w j))
  · exact hasDerivAt_const q.1 (w i + 0 + 0)

theorem hasDerivAt_twoParameterInsert_tail {d : ℕ} (w : Aux (d + 1))
    (j : Fin (d + 1)) (q : Plane) :
    HasDerivAt (fun s => twoParameterInsert w j (q.1, s)) (Pi.single j 1) q.2 := by
  apply hasDerivAt_pi.mpr
  intro i
  simp only [twoParameterInsert, Pi.add_apply, Pi.single_apply]
  split_ifs
  · simpa only [id_eq] using ((hasDerivAt_id q.2).sub_const (w j)).const_add
      (w i + (q.1 - w 0))
  · exact hasDerivAt_const q.2 (w i + (q.1 - w 0) + 0)
  · simpa only [id_eq] using ((hasDerivAt_id q.2).sub_const (w j)).const_add (w i + 0)
  · exact hasDerivAt_const q.2 (w i + 0 + 0)

namespace ProjectionModel
variable {d : ℕ} (D : ProjectionModel d)

def twoSliceCurves (j : Fin (d + 1)) (p : ℝ × Plane) : ℝ :=
  D.h p.1 (twoParameterInsert D.base.2 j p.2)

def twoSliceCenters (j : Fin (d + 1)) (p : ℝ × Plane) : ℝ :=
  D.κ (p.1, twoParameterInsert D.base.2 j p.2)

theorem twoSliceCenters_normalize (j : Fin (d + 1)) (hj : j ≠ 0)
    (q : Plane) (hq : twoParameterInsert D.base.2 j q ∈ ball D.base.2 D.radius) :
    D.twoSliceCenters j (D.base.1, q) = q.1 := by
  rw [twoSliceCenters, D.normalize _ hq, twoParameterInsert_head _ _ hj]

theorem twoSliceCurves_analyticAt (j : Fin (d + 1)) (p : ℝ × Plane)
    (hp : p.1 ∈ D.I.carrier)
    (hq : twoParameterInsert D.base.2 j p.2 ∈ ball D.base.2 D.radius) :
    AnalyticAt ℝ (D.twoSliceCurves j) p := by
  exact (D.h_analytic _ ⟨hp, hq⟩).comp
    (f := fun p : ℝ × Plane => (p.1, twoParameterInsert D.base.2 j p.2))
      (analyticAt_fst.prod (((twoParameterInsert_analytic D.base.2 j) p.2
        (mem_univ _)).comp analyticAt_snd))

theorem twoSliceCenters_analyticAt (j : Fin (d + 1)) (p : ℝ × Plane)
    (hp : p.1 ∈ ball D.base.1 D.radius)
    (hq : twoParameterInsert D.base.2 j p.2 ∈ ball D.base.2 D.radius) :
    AnalyticAt ℝ (D.twoSliceCenters j) p := by
  exact (D.κ_analytic _ ⟨hp, hq⟩).comp
    (f := fun p : ℝ × Plane => (p.1, twoParameterInsert D.base.2 j p.2))
      (analyticAt_fst.prod (((twoParameterInsert_analytic D.base.2 j) p.2
        (mem_univ _)).comp analyticAt_snd))

theorem twoSliceCurves_headDerivative (j : Fin (d + 1)) (p : ℝ × Plane)
    (hp : p.1 ∈ D.I.carrier)
    (hq : twoParameterInsert D.base.2 j p.2 ∈ ball D.base.2 D.radius) :
    scalarHeadDerivative (D.twoSliceCurves j) p =
      D.variationColumn 0 (p.1, twoParameterInsert D.base.2 j p.2) := by
  have hψ := (D.twoSliceCurves_analyticAt j p hp hq).differentiableAt
  have hslice : HasDerivAt (fun y => D.twoSliceCurves j (p.1, (y, p.2.2)))
      (D.variationColumn 0 (p.1, twoParameterInsert D.base.2 j p.2)) p.2.1 := by
    exact (D.h_analytic (p.1, twoParameterInsert D.base.2 j p.2) ⟨hp, hq⟩).differentiableAt.hasFDerivAt.comp_hasDerivAt p.2.1
      ((hasDerivAt_const p.2.1 p.1).prodMk
        (hasDerivAt_twoParameterInsert_head D.base.2 j p.2))
  have hi : HasDerivAt (fun y : ℝ => (p.1, (y, p.2.2)))
      ((0, (1, 0)) : ℝ × Plane) p.2.1 :=
    (hasDerivAt_const p.2.1 p.1).prodMk
      ((hasDerivAt_id p.2.1).prodMk (hasDerivAt_const p.2.1 p.2.2))
  exact ((hψ.hasFDerivAt.comp_hasDerivAt
    (f := fun y : ℝ => (p.1, (y, p.2.2))) _ hi).unique hslice)

theorem twoSliceCurves_tailDerivative (j : Fin (d + 1)) (p : ℝ × Plane)
    (hp : p.1 ∈ D.I.carrier)
    (hq : twoParameterInsert D.base.2 j p.2 ∈ ball D.base.2 D.radius) :
    scalarTailDerivative (D.twoSliceCurves j) p =
      D.variationColumn j (p.1, twoParameterInsert D.base.2 j p.2) := by
  have hψ := (D.twoSliceCurves_analyticAt j p hp hq).differentiableAt
  have hslice : HasDerivAt (fun s => D.twoSliceCurves j (p.1, (p.2.1, s)))
      (D.variationColumn j (p.1, twoParameterInsert D.base.2 j p.2)) p.2.2 := by
    exact (D.h_analytic (p.1, twoParameterInsert D.base.2 j p.2) ⟨hp, hq⟩).differentiableAt.hasFDerivAt.comp_hasDerivAt p.2.2
      ((hasDerivAt_const p.2.2 p.1).prodMk
        (hasDerivAt_twoParameterInsert_tail D.base.2 j p.2))
  have hi : HasDerivAt (fun s : ℝ => (p.1, (p.2.1, s)))
      ((0, (0, 1)) : ℝ × Plane) p.2.2 :=
    (hasDerivAt_const p.2.2 p.1).prodMk
      ((hasDerivAt_const p.2.2 p.2.1).prodMk (hasDerivAt_id p.2.2))
  exact ((hψ.hasFDerivAt.comp_hasDerivAt
    (f := fun s : ℝ => (p.1, (p.2.1, s))) _ hi).unique hslice)

/-- The general stationary-branch theorem applies to the actual normal
form, with the unused coordinates fixed at the model's base point. -/
theorem twoSliceCenters_independent_tail_of_stationary
    (j : Fin (d + 1)) (hj : j ≠ 0) {X Y S : Set ℝ}
    (hX : IsOpen X) (hXc : IsPreconnected X) (hY : IsOpen Y)
    (hS : IsOpen S) (hSc : IsPreconnected S)
    (hb : D.base.1 ∈ X) (hXB : X ⊆ ball D.base.1 D.radius)
    (hQB : ∀ q ∈ Y ×ˢ S, twoParameterInsert D.base.2 j q ∈ ball D.base.2 D.radius)
    (hh : ∀ p ∈ X ×ˢ (Y ×ˢ S), scalarHeadDerivative (D.twoSliceCenters j) p ≠ 0)
    (hst : ∀ q ∈ Y ×ˢ S, ∀ x ∈ X,
      deriv (fun a => scalarGradientSlope (D.twoSliceCenters j) (a, q)) x = 0)
    (x : ℝ) (hx : x ∈ X) (y : ℝ) (hy : y ∈ Y)
    (s s₀ : ℝ) (hs : s ∈ S) (hs₀ : s₀ ∈ S) :
    D.twoSliceCenters j (x, (y, s)) = D.twoSliceCenters j (x, (y, s₀)) := by
  exact scalar_stationary_independent_tail hX hXc hY hS hSc D.base.1 hb
    (fun p hp => D.twoSliceCenters_analyticAt j p (hXB hp.1) (hQB p.2 hp.2))
      (fun q hq => D.twoSliceCenters_normalize j hj q (hQB q hq)) hh hst
        x hx y hy s s₀ hs hs₀

end ProjectionModel
end PlanarNikodym
