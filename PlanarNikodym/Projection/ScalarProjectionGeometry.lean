import PlanarNikodym.Avoidance.AvoidanceJets

/-! The two-dimensional scalar projection used in §7.3, Steps 1–2.

The rank of the actual function-valued derivative forces every pair of
coordinate variations to rotate projectively at some interior time.
These are local geometric preparation results, not a construction of a
Nikodym set or an instance of `ProjectionConstructionInput`. -/

noncomputable section
open Set Filter Function MeasureTheory Metric
open scoped Topology Matrix
namespace PlanarNikodym.ProjectionModel

variable {d : ℕ} (D : ProjectionModel d)

/-- A two-column certificate for change of projective gradient direction. -/
def pairVariationDet (i j : Fin (d + 1)) (x : ℝ × Aux (d + 1)) : ℝ :=
  D.variationColumn i x * timeDerivative (D.variationColumn j) 1 x -
    D.variationColumn j x * timeDerivative (D.variationColumn i) 1 x

theorem pairVariationDet_analyticAt {x : ℝ × Aux (d + 1)}
    (hx : x ∈ D.I.carrier ×ˢ ball D.base.2 D.radius) (i j : Fin (d + 1)) :
    AnalyticAt ℝ (D.pairVariationDet i j) x :=
  ((D.variationColumn_analyticAt hx i).mul
    (timeDerivative_analyticAt (D.variationColumn_analyticAt hx j) 1)).sub
      ((D.variationColumn_analyticAt hx j).mul
        (timeDerivative_analyticAt (D.variationColumn_analyticAt hx i) 1))

theorem pairVariationDet_eq_wronskian (i j : Fin (d + 1))
    (w : Aux (d + 1)) (hw : w ∈ ball D.base.2 D.radius)
    (t : ℝ) (ht : t ∈ D.I.carrier) :
    D.pairVariationDet i j (t, w) =
      wronskian (fun a s => D.variationColumn (if a = (0 : Fin 2) then i else j) (s, w)) t := by
  simp only [pairVariationDet, wronskian, Matrix.det_fin_two]
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero, Fin.val_zero, Fin.val_one, iteratedDeriv_zero,
    iteratedDeriv_one, timeDerivative_eq_iteratedDeriv 1 (t, w)
      (D.variationColumn_analyticAt ⟨ht, hw⟩ i),
    timeDerivative_eq_iteratedDeriv 1 (t, w)
      (D.variationColumn_analyticAt ⟨ht, hw⟩ j)]

theorem pairVariationColumns_independent (i j : Fin (d + 1)) (hij : i ≠ j)
    (w : Aux (d + 1)) (hw : w ∈ ball D.base.2 D.radius) :
    LinearIndependent ℝ (fun a (t : D.I.carrier) =>
      D.variationColumn (if a = (0 : Fin 2) then i else j) (t, w)) := by
  apply (D.variationColumns_independent w hw).comp
    (fun a : Fin 2 => if a = 0 then i else j)
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

/-- The full-rank hypothesis forces projective variation already on any
two distinct parameter directions. -/
theorem exists_pairVariationDet_ne_zero (i j : Fin (d + 1)) (hij : i ≠ j)
    (w : Aux (d + 1)) (hw : w ∈ ball D.base.2 D.radius) :
    ∃ t ∈ D.I.carrier, D.pairVariationDet i j (t, w) ≠ 0 := by
  have ha : ∀ a : Fin 2, AnalyticOnNhd ℝ
      (fun t => D.variationColumn (if a = 0 then i else j) (t, w)) D.I.carrier := by
    intro a t ht
    exact (D.variationColumn_analyticAt ⟨ht, hw⟩ _).comp
      (f := fun t : ℝ => (t, w)) (analyticAt_id.prod analyticAt_const)
  obtain ⟨t, ht, hdet⟩ := bocher_input 2 D.I _ ha
    (D.pairVariationColumns_independent i j hij w hw)
  exact ⟨t, ht, by rwa [D.pairVariationDet_eq_wronskian i j w hw t ht]⟩

theorem exists_variationColumn_ne_zero (j : Fin (d + 1))
    (w : Aux (d + 1)) (hw : w ∈ ball D.base.2 D.radius) :
    ∃ t ∈ D.I.carrier, D.variationColumn j (t, w) ≠ 0 := by
  by_contra hn
  have hz : (fun t : D.I.carrier => D.variationColumn j (t, w)) = 0 := by
    ext t
    exact not_ne_iff.mp (fun h => hn ⟨t, t.property, h⟩)
  exact (D.variationColumns_independent w hw).ne_zero j hz

/-- One can choose the interior time with the selected scalar derivative
nonzero as well as the two-column rotation determinant nonzero. -/
theorem exists_interior_pairVariationDet_and_column_ne_zero
    (i j : Fin (d + 1)) (hij : i ≠ j)
    (w : Aux (d + 1)) (hw : w ∈ ball D.base.2 D.radius) :
    ∃ t ∈ Ioo D.I.left D.I.right,
      D.pairVariationDet i j (t, w) ≠ 0 ∧ D.variationColumn j (t, w) ≠ 0 := by
  let A : ℝ → ℝ := fun t => D.pairVariationDet i j (t, w)
  let B : ℝ → ℝ := fun t => D.variationColumn j (t, w)
  have hA : AnalyticOnNhd ℝ A D.I.carrier := fun t ht =>
    (D.pairVariationDet_analyticAt ⟨ht, hw⟩ i j).comp
      (f := fun t : ℝ => (t, w)) (analyticAt_id.prod analyticAt_const)
  have hB : AnalyticOnNhd ℝ B D.I.carrier := fun t ht =>
    (D.variationColumn_analyticAt ⟨ht, hw⟩ j).comp
      (f := fun t : ℝ => (t, w)) (analyticAt_id.prod analyticAt_const)
  have hAB : ∃ t ∈ D.I.carrier, A t * B t ≠ 0 := by
    by_contra hn
    have hz : EqOn (A * B) 0 D.I.carrier := by
      intro t ht
      exact not_ne_iff.mp (fun h => hn ⟨t, ht, h⟩)
    rcases hA.eq_zero_or_eq_zero_of_mul_eq_zero hB hz isPreconnected_Icc with h | h
    · obtain ⟨t, ht, hne⟩ := D.exists_pairVariationDet_ne_zero i j hij w hw
      exact hne (h t ht)
    · obtain ⟨t, ht, hne⟩ := D.exists_variationColumn_ne_zero j w hw
      exact hne (h t ht)
  obtain ⟨t, ht, hne⟩ := exists_interior_ne_zero D.I (A * B)
    (fun t ht => ((hA t ht).mul (hB t ht)).continuousAt) hAB
  exact ⟨t, ht, (mul_ne_zero_iff.mp hne).1, (mul_ne_zero_iff.mp hne).2⟩

/-- Both nonvanishing conditions hold on an actual product neighbourhood
inside the analytic domain. This supplies a common local patch for the
scalar Kakeya construction and the prescribed projection branch. -/
theorem exists_pair_projection_patch (i j : Fin (d + 1)) (hij : i ≠ j)
    (w : Aux (d + 1)) (hw : w ∈ ball D.base.2 D.radius) :
    ∃ t ∈ Ioo D.I.left D.I.right, ∃ r : ℝ, 0 < r ∧
      ball t r ⊆ Ioo D.I.left D.I.right ∧
      ball w r ⊆ ball D.base.2 D.radius ∧
      ∀ s ∈ ball t r, ∀ v ∈ ball w r,
        D.pairVariationDet i j (s, v) ≠ 0 ∧ D.variationColumn j (s, v) ≠ 0 := by
  obtain ⟨t, ht, hdet, hcol⟩ :=
    D.exists_interior_pairVariationDet_and_column_ne_zero i j hij w hw
  have hdom : (t, w) ∈ D.I.carrier ×ˢ ball D.base.2 D.radius :=
    ⟨⟨ht.1.le, ht.2.le⟩, hw⟩
  have hN : ∀ᶠ p in 𝓝 (t, w),
      p ∈ Ioo D.I.left D.I.right ×ˢ ball D.base.2 D.radius ∧
      D.pairVariationDet i j p ≠ 0 ∧ D.variationColumn j p ≠ 0 := by
    filter_upwards [(isOpen_Ioo.prod isOpen_ball).mem_nhds ⟨ht, hw⟩,
      (D.pairVariationDet_analyticAt hdom i j).continuousAt.eventually_ne hdet,
      (D.variationColumn_analyticAt hdom j).continuousAt.eventually_ne hcol]
      with p hp hd hc
    exact ⟨hp, hd, hc⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hN
  have hprod : ball t r ×ˢ ball w r ⊆
      {p | p ∈ Ioo D.I.left D.I.right ×ˢ ball D.base.2 D.radius ∧
        D.pairVariationDet i j p ≠ 0 ∧ D.variationColumn j p ≠ 0} := by
    rw [ball_prod_same]
    exact hball
  refine ⟨t, ht, r, hr, ?_, ?_, ?_⟩
  · intro s hs
    exact (hprod (a := (s, w)) ⟨hs, mem_ball_self hr⟩).1.1
  · intro v hv
    exact (hprod (a := (t, v)) ⟨mem_ball_self hr, hv⟩).1.2
  · intro s hs v hv
    exact (hprod ⟨hs, hv⟩).2

end PlanarNikodym.ProjectionModel
