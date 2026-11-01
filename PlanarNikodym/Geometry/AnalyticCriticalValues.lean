import PlanarNikodym.Geometry.CountableAnalyticZeroCharts
import Mathlib.Analysis.Calculus.MeanValue

/-! Scalar analytic critical values are countable in every finite dimension.
The proof actually lowers source dimension on countably many analytic charts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped Topology
namespace PlanarNikodym

theorem countable_image_of_locally_countable_image
    {X Y : Type*} [TopologicalSpace X] [HereditarilyLindelofSpace X]
    (f : X → Y) (S : Set X)
    (h : ∀ x ∈ S, ∃ U, IsOpen U ∧ x ∈ U ∧ (f '' (S ∩ U)).Countable) :
    (f '' S).Countable := by
  classical
  choose U hUo hxU hUc using fun x : S => h x.1 x.2
  obtain ⟨T, hTc, hcover⟩ := (HereditarilyLindelofSpace.isLindelof S).elim_countable_subcover
    U hUo (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  apply (hTc.biUnion fun x _ => hUc x).mono
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hx)
  exact mem_iUnion₂.mpr ⟨y, hy, mem_image_of_mem f ⟨hx, hxy⟩⟩

theorem exists_coordinate_derivative_ne_zero {n : ℕ}
    (L : Aux n →L[ℝ] ℝ) (hL : L ≠ 0) :
    ∃ j : Fin n, L (Pi.single j 1) ≠ 0 := by
  classical
  by_contra! h
  apply hL
  have hl : L.toLinearMap = 0 := by
    apply LinearMap.pi_ext
    intro j c
    change L (Pi.single j c) = 0
    have hs : Pi.single j c = c • Pi.single j (1 : ℝ) := by
      ext k
      by_cases hk : k = j <;> simp [hk]
    rw [hs, map_smul, h j, smul_zero]
  ext v
  exact LinearMap.congr_fun hl v

/-- Actual critical values of an analytic real-valued function on an arbitrary
open subset of Euclidean space form a countable set. -/
theorem analytic_critical_values_countable (n : ℕ)
    (f : Aux n → ℝ) {U : Set (Aux n)} (ho : IsOpen U)
    (ha : AnalyticOnNhd ℝ f U) :
    (f '' {x | x ∈ U ∧ fderiv ℝ f x = 0}).Countable := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      exact (Set.to_countable _).image f
    | succ n =>
      apply countable_image_of_locally_countable_image
      intro x hx
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp ho x hx.1
      have hab : AnalyticOnNhd ℝ f (ball x r) := ha.mono hball
      have hcount :
          (f '' {y | y ∈ ball x r ∧ fderiv ℝ f y = 0}).Countable := by
        by_cases hz : ∀ y ∈ ball x r, fderiv ℝ f y = 0
        · obtain ⟨c, hc⟩ := isOpen_ball.exists_is_const_of_fderiv_eq_zero
            (convex_ball x r).isPreconnected
            (fun y hy => (hab y hy).differentiableAt.differentiableWithinAt) hz
          apply (Set.countable_singleton c).mono
          rintro _ ⟨y, hy, rfl⟩
          exact hc y hy.1
        · push Not at hz
          obtain ⟨y, hy, hdy⟩ := hz
          obtain ⟨j, hj⟩ := exists_coordinate_derivative_ne_zero (fderiv ℝ f y) hdy
          let s : Fin 0 → Fin (n + 1) := Fin.elim0
          let g := coordinateJet f 1 (Fin.cons j s)
          have hg : AnalyticOnNhd ℝ g (ball x r) :=
            coordinateJet_analytic hab 1 _
          have hgval (z : Aux (n + 1)) (hz : z ∈ ball x r) :
              g z = fderiv ℝ f z (Pi.single j 1) :=
            coordinateJet_cons hab s j hz
          obtain ⟨C, hC, _, hcov⟩ := exists_countable_analytic_zero_charts g isOpen_ball hg
            (convex_ball x r).isPreconnected ⟨y, hy, by rwa [hgval y hy]⟩
          have hlocal (Q : AnalyticDimensionDropChart (n + 1) (ball x r)) :
              ((f ∘ Q.map) '' {v | v ∈ Q.source ∧ fderiv ℝ (f ∘ Q.map) v = 0}).Countable :=
            ih Q.dim Q.dim_lt (f ∘ Q.map) Q.open_source
              (fun v hv => (hab (Q.map v) (Q.maps_to hv)).comp (Q.analytic_map v hv))
          apply (hC.biUnion fun Q _ => hlocal Q).mono
          rintro _ ⟨z, hz, rfl⟩
          have hgz : g z = 0 := by rw [hgval z hz.1, hz.2]; rfl
          obtain ⟨Q, hQ, v, hv, he⟩ := hcov z hz.1 hgz
          refine mem_iUnion₂.mpr ⟨Q, hQ, v, ⟨hv, ?_⟩, congrArg f he⟩
          ·
            rw [fderiv_comp v (hab (Q.map v) (Q.maps_to hv)).differentiableAt
              (Q.analytic_map v hv).differentiableAt, he, hz.2, ContinuousLinearMap.zero_comp]
      refine ⟨ball x r, isOpen_ball, mem_ball_self hr, hcount.mono ?_⟩
      rintro _ ⟨y, ⟨hy, hyb⟩, rfl⟩
      exact mem_image_of_mem f ⟨hyb, hy.2⟩

/-- For an analytic vector-valued map, the image of the actual zero-differential
locus is countable, with no restriction on the source dimension. -/
theorem analytic_zero_differential_image_countable {n m : ℕ}
    (f : Aux n → Base m) {U : Set (Aux n)} (ho : IsOpen U)
    (ha : AnalyticOnNhd ℝ f U) :
    (f '' {x | x ∈ U ∧ fderiv ℝ f x = 0}).Countable := by
  let C (i : Fin m) :=
    (fun x => f x i) '' {x | x ∈ U ∧ fderiv ℝ (fun y => f y i) x = 0}
  have hC (i : Fin m) : (C i).Countable :=
    analytic_critical_values_countable n (fun x => f x i) ho
      (fun x hx => ((ContinuousLinearMap.proj i : Base m →L[ℝ] ℝ).analyticAt _).comp
        (ha x hx))
  apply (Set.countable_pi hC).mono
  rintro _ ⟨x, hx, rfl⟩ i
  refine ⟨x, ⟨hx.1, ?_⟩, rfl⟩
  change fderiv ℝ ((ContinuousLinearMap.proj i : Base m →L[ℝ] ℝ) ∘ f) x = 0
  rw [fderiv_comp x (ContinuousLinearMap.proj i).differentiableAt
    (ha x hx.1).differentiableAt, hx.2, ContinuousLinearMap.comp_zero]

end PlanarNikodym
