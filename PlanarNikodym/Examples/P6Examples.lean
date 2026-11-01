import PlanarNikodym.Classification.GeneralClassification
import PlanarNikodym.Geometry.ZeroAuxMeasurability
import PlanarNikodym.Examples.ClassificationExamples
import Mathlib.Analysis.Convex.PathConnected

noncomputable section
open Set MeasureTheory Metric
namespace PlanarNikodym.Examples

abbrev boundedHorizontal (I : Interval) : Family 2 0 :=
  (horizontal I).restrictTo (ball 0 1)

def horizontalBand (i : Fin 2) : Set (Parameters 2 0) :=
  ball 0 1 ∩ {p | if i = 0 then 0 < p.1 0 else p.1 0 < 0}

theorem horizontalBand_open (i : Fin 2) : IsOpen (horizontalBand i) := by
  have hc : Continuous (fun p : Parameters 2 0 => p.1 0) :=
    (ContinuousLinearMap.proj (0 : Fin 2) : Base 2 →L[ℝ] ℝ).continuous.comp continuous_fst
  fin_cases i
  · exact isOpen_ball.inter (isOpen_lt continuous_const hc)
  · exact isOpen_ball.inter (isOpen_lt hc continuous_const)

theorem horizontalBand_connected (i : Fin 2) : IsConnected (horizontalBand i) := by
  have hl : IsLinearMap ℝ (fun p : Parameters 2 0 => p.1 0) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hconv : Convex ℝ (horizontalBand i) := by
    fin_cases i
    · exact (convex_ball (0 : Parameters 2 0) 1).inter (convex_halfSpace_gt hl 0)
    · exact (convex_ball (0 : Parameters 2 0) 1).inter (convex_halfSpace_lt hl 0)
  apply hconv.isConnected
  fin_cases i
  · refine ⟨((fun _ => 1 / 2), 0), ?_, by norm_num⟩
    norm_num [mem_ball, dist_eq_norm, Prod.norm_def, pi_norm_const]
  · refine ⟨((fun _ => -(1 / 2)), 0), ?_, by norm_num⟩
    norm_num [mem_ball, dist_eq_norm, Prod.norm_def, pi_norm_const]

def horizontalBandPiece (I : Interval) (i : Fin 2) : RankPiece (boundedHorizontal I) where
  toAnalyticPiece := AnalyticPiece.restrict (boundedHorizontal I) (horizontalBand i)
    (horizontalBand_open i) (isBounded_ball.subset inter_subset_left) (horizontalBand_connected i)
    ((horizontal_analytic I).restrictTo (subset_univ _)) inter_subset_left
  point_rank := 0
  curve_rank := 1
  ranks := fun p _ => horizontal_ranks I p
  centers_measurable := zero_aux_centers_measurable _ (horizontalBand_open i).measurableSet (by
    intro t _
    exact (ContinuousLinearMap.proj (1 : Fin 2) : Base 2 →L[ℝ] ℝ).continuous.comp continuous_fst)

def verticalException : Set (Base 2) := {z | z 0 = 0}

theorem verticalException_closed : IsClosed verticalException :=
  isClosed_eq (ContinuousLinearMap.proj (0 : Fin 2) : Base 2 →L[ℝ] ℝ).continuous continuous_const

theorem verticalException_null : volume verticalException = 0 := by
  let K := centerCoordinates (1 : Fin 2)
  let A : Set Plane := ({0} : Set ℝ) ×ˢ univ
  have hA : volume A = 0 := by
    change (volume.prod volume) (({0} : Set ℝ) ×ˢ univ) = 0
    rw [Measure.prod_prod, measure_singleton, zero_mul]
  have he : K '' A = verticalException := by
    ext z
    constructor
    · rintro ⟨⟨x, y⟩, ⟨hx, _⟩, rfl⟩
      change centerCoordinates (1 : Fin 2) (x, y) 0 = 0
      simpa only [centerCoordinates_apply, Fin.zero_ne_one, if_false] using mem_singleton_iff.mp hx
    · intro hz
      refine ⟨(0, z 1), ⟨by simp, mem_univ _⟩, ?_⟩
      ext i
      fin_cases i
      · simpa [K, centerCoordinates_apply] using hz.symm
      · simp [K, centerCoordinates_apply]
  rw [← he]
  exact linearEquiv_image_null K volume volume A hA

/-- A genuine two-piece certificate with a nonempty exceptional centre
line. This exercises finite selection and the closed-null-exception argument
without assuming the abstract tame-geometry input. -/
def horizontalSplit (I : Interval) : RankDecomposition (boundedHorizontal I) where
  count := 2
  piece := horizontalBandPiece I
  exceptional := verticalException
  closed_exceptional := verticalException_closed
  null_exceptional := verticalException_null
  cover := by
    intro p hp
    by_cases hz : p.1 0 = 0
    · exact Or.inl hz
    · by_cases hpos : 0 < p.1 0
      · exact Or.inr ⟨0, p, ⟨hp, hpos⟩, rfl⟩
      · exact Or.inr ⟨1, p, ⟨hp, lt_of_le_of_ne (le_of_not_gt hpos) hz⟩, rfl⟩
  disjoint := by
    intro i j hn
    fin_cases i <;> fin_cases j
    · exact (hn rfl).elim
    · change Disjoint (id '' horizontalBand 0) (id '' horizontalBand 1)
      rw [image_id, image_id]
      apply disjoint_left.mpr
      intro p hp hq
      have hpos : 0 < p.1 0 := by simpa using hp.2
      have hneg : p.1 0 < 0 := by simpa using hq.2
      exact (not_lt_of_gt hpos) hneg
    · change Disjoint (id '' horizontalBand 1) (id '' horizontalBand 0)
      rw [image_id, image_id]
      apply disjoint_left.mpr
      intro p hp hq
      have hpos : 0 < p.1 0 := by simpa using hq.2
      have hneg : p.1 0 < 0 := by simpa using hp.2
      exact (not_lt_of_gt hpos) hneg
    · exact (hn rfl).elim

theorem horizontalSplit_proposition16 (inputs : P5Inputs) (I : Interval) :
    (horizontalSplit I).Proposition16Conclusions :=
  (horizontalSplit I).proposition_1_6_of_decomposition inputs
    ((horizontal_analytic I).restrictTo (subset_univ _))

theorem horizontalSplit_exceptional_partition (I : Interval) :
    (boundedHorizontal I).W =
      (⋃ i, ((horizontalSplit I).piece i).toAnalyticPiece.image) ∪ (horizontalSplit I).remainder ∧
      volume (closure (Prod.fst '' (horizontalSplit I).remainder)) = 0 :=
  ⟨(horizontalSplit I).partition, (horizontalSplit I).remainder_centers_closure_null⟩

theorem unbounded_horizontal_general_classification (inputs : P6Inputs) (I : Interval) :
    (horizontal I).AdmitsNikodym ↔
      (horizontal I).HasMassiveCurveReuse ∨ (horizontal I).LocalReuseNotCovered :=
  general_classification_of_analytic inputs (horizontal I) isOpen_univ (horizontal_analytic I)

theorem empty_domain_general_classification (I : Interval) :
    let G : Family 2 3 := ⟨I, ∅, fun t p => t + p.1 0 + p.2 0⟩
    G.AdmitsNikodym ↔ G.HasMassiveCurveReuse ∨ G.LocalReuseNotCovered := by
  exact Family.classification_of_empty _ rfl

end PlanarNikodym.Examples
