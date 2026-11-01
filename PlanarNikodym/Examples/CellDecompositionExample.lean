import PlanarNikodym.Cells.CompatibleCellGeometry
import PlanarNikodym.Examples.P6Examples

noncomputable section
open Set Submodule Module MeasureTheory Metric
namespace PlanarNikodym.Examples

/-- A bounded family whose point rank drops on a hypersurface with every
centre present. That hypersurface must be retained as a lower-dimensional
piece, rather than discarded as a null set of centres. -/
abbrev quadraticSlide (I : Interval) : Family 2 1 :=
  ⟨I, ball 0 1, fun _ p => p.1 1 - (p.2 0) ^ 2⟩

theorem quadraticSlide_analytic (I : Interval) : (quadraticSlide I).IsAnalytic := by
  intro p _
  have hz : AnalyticAt ℝ (fun x : ℝ × Parameters 2 1 => x.2.1) p :=
    analyticAt_fst.comp analyticAt_snd
  have hu : AnalyticAt ℝ (fun x : ℝ × Parameters 2 1 => x.2.2) p :=
    analyticAt_snd.comp analyticAt_snd
  exact (((ContinuousLinearMap.proj 1 : Base 2 →L[ℝ] ℝ).analyticAt _).comp hz).sub
    ((((ContinuousLinearMap.proj 0 : Aux 1 →L[ℝ] ℝ).analyticAt _).comp hu).pow 2)

theorem quadraticSlide_uColumn (I : Interval) (p : Parameters 2 1) :
    (quadraticSlide I).uColumn p = ![fun _ : I.carrier => -(2 * p.2 0)] := by
  funext i t
  change fderiv ℝ (fun u : Aux 1 => p.1 1 - (u 0) ^ 2) p.2 (Pi.single i 1) = _
  have hd := (hasFDerivAt_const (𝕜 := ℝ) (p.1 1) p.2).sub
    ((hasFDerivAt_apply (𝕜 := ℝ) 0 p.2).pow 2)
  change HasFDerivAt (fun u : Aux 1 => p.1 1 - (u 0) ^ 2) _ p.2 at hd
  rw [hd.fderiv]
  fin_cases i
  simp

theorem quadraticSlide_zColumn (I : Interval) (p : Parameters 2 1) :
    (quadraticSlide I).zColumn p = ![fun _ : I.carrier => 0, fun _ => 1] := by
  funext i t
  change fderiv ℝ (fun z : Base 2 => z 1 - (p.2 0) ^ 2) p.1 (Pi.single i 1) = _
  have hd := (hasFDerivAt_apply (𝕜 := ℝ) 1 p.1).sub
    (hasFDerivAt_const (𝕜 := ℝ) ((p.2 0) ^ 2) p.1)
  change HasFDerivAt (fun z : Base 2 => z 1 - (p.2 0) ^ 2) _ p.1 at hd
  rw [hd.fderiv]
  fin_cases i <;> simp

theorem quadraticSlide_regular_ranks (I : Interval) (p : Parameters 2 1) (hp : p.2 0 ≠ 0) :
    (quadraticSlide I).pointRank p = 1 ∧ (quadraticSlide I).curveRank p = 1 := by
  have hpoint : (quadraticSlide I).pointRank p = 1 := by
    rw [Family.pointRank, Family.pointSpace, quadraticSlide_uColumn, Set.range_unique]
    apply finrank_span_singleton
    intro he
    have hx := congrFun he ⟨I.left, le_rfl, I.nondegenerate.le⟩
    change -(2 * p.2 0) = 0 at hx
    exact hp (by linarith)
  refine ⟨hpoint, ?_⟩
  have hspace : (quadraticSlide I).curveSpace p = ℝ ∙ (1 : I.carrier → ℝ) := by
    apply le_antisymm
    · apply sup_le <;> apply span_le.mpr
      · rintro _ ⟨i, rfl⟩
        rw [quadraticSlide_uColumn]
        fin_cases i
        change (fun _ : I.carrier => -(2 * p.2 0)) ∈ ℝ ∙ (1 : I.carrier → ℝ)
        rw [Submodule.mem_span_singleton]
        exact ⟨-(2 * p.2 0), by ext t; simp⟩
      · rintro _ ⟨i, rfl⟩
        rw [quadraticSlide_zColumn]
        fin_cases i
        · exact zero_mem _
        · exact mem_span_singleton_self _
    · apply (span_singleton_le_iff_mem _ _).mpr
      apply Submodule.mem_sup_right
      exact subset_span ⟨1, by rw [quadraticSlide_zColumn]; rfl⟩
  rw [Family.curveRank, hspace]
  exact finrank_span_singleton (one_function_ne_zero I)

def quadraticBand (i : Fin 2) : Set (Parameters 2 1) :=
  ball 0 1 ∩ {p | if i = 0 then 0 < p.2 0 else p.2 0 < 0}

theorem quadraticBand_open (i : Fin 2) : IsOpen (quadraticBand i) := by
  have hc : Continuous (fun p : Parameters 2 1 => p.2 0) :=
    (ContinuousLinearMap.proj (0 : Fin 1) : Aux 1 →L[ℝ] ℝ).continuous.comp continuous_snd
  fin_cases i
  · exact isOpen_ball.inter (isOpen_lt continuous_const hc)
  · exact isOpen_ball.inter (isOpen_lt hc continuous_const)

theorem quadraticBand_connected (i : Fin 2) : IsConnected (quadraticBand i) := by
  have hl : IsLinearMap ℝ (fun p : Parameters 2 1 => p.2 0) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hconv : Convex ℝ (quadraticBand i) := by
    fin_cases i
    · exact (convex_ball (0 : Parameters 2 1) 1).inter (convex_halfSpace_gt hl 0)
    · exact (convex_ball (0 : Parameters 2 1) 1).inter (convex_halfSpace_lt hl 0)
  apply hconv.isConnected
  fin_cases i
  · refine ⟨(0, fun _ => 1 / 2), ?_, by norm_num⟩
    norm_num [mem_ball, dist_eq_norm, Prod.norm_def, pi_norm_const]
  · refine ⟨(0, fun _ => -(1 / 2)), ?_, by norm_num⟩
    norm_num [mem_ball, dist_eq_norm, Prod.norm_def, pi_norm_const]

abbrev quadraticBandPiece (I : Interval) (i : Fin 2) : AnalyticPiece (quadraticSlide I) :=
  AnalyticPiece.restrict _ (quadraticBand i) (quadraticBand_open i)
    (isBounded_ball.subset inter_subset_left) (quadraticBand_connected i)
    ((quadraticSlide_analytic I).restrictTo inter_subset_left) inter_subset_left

abbrev quadraticZeroPiece (I : Interval) : AnalyticPiece (quadraticSlide I) where
  dim := 0
  dim_le := by omega
  family := boundedHorizontal I
  interval_eq := rfl
  open_domain := isOpen_ball
  bounded_domain := isBounded_ball
  connected_domain := (convex_ball (0 : Parameters 2 0) 1).isConnected (by
    exact ⟨0, mem_ball_self (by norm_num)⟩)
  analytic_family := (horizontal_analytic I).restrictTo (subset_univ _)
  embed p := (p.1, 0)
  inverse p := (p.1, 0)
  analytic_embed := fun _ _ => analyticAt_fst.prod analyticAt_const
  continuous_inverse := (continuous_fst.prodMk continuous_const).continuousOn
  left_inv := by intro p _; exact Prod.ext rfl (Subsingleton.elim _ _)
  keep_center := fun _ _ => rfl
  maps_to := by
    intro p hp
    change p ∈ ball (0 : Parameters 2 0) 1 at hp
    have hp' : ‖p.1‖ < 1 := lt_of_le_of_lt (norm_fst_le p)
      (by simpa only [mem_ball, dist_zero_right] using hp)
    change (p.1, (0 : Aux 1)) ∈ ball (0 : Parameters 2 1) 1
    simpa only [mem_ball, dist_zero_right, Prod.norm_def, norm_zero,
      max_eq_left (norm_nonneg _)] using hp'
  identity := by intro p _ t _; simp

theorem quadraticZeroPiece_center_image (I : Interval) :
    Prod.fst '' (quadraticZeroPiece I).image = ball (0 : Base 2) 1 := by
  ext z
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    change q.1 ∈ ball (0 : Base 2) 1
    rw [mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (norm_fst_le q) (by
      simpa only [mem_ball, dist_zero_right] using hq)
  · intro hz
    refine ⟨(z, 0), ⟨(z, 0), ?_, rfl⟩, rfl⟩
    change (z, (0 : Aux 0)) ∈ ball (0 : Parameters 2 0) 1
    simpa only [mem_ball, dist_zero_right, Prod.norm_def, norm_zero,
      max_eq_left (norm_nonneg _)] using hz

theorem quadraticZeroPiece_centers_positive (I : Interval) :
    0 < volume (Prod.fst '' (quadraticZeroPiece I).image) := by
  rw [quadraticZeroPiece_center_image]
  exact isOpen_ball.measure_pos (μ := volume) ⟨0, mem_ball_self (by norm_num)⟩

abbrev quadraticCellPiece (I : Interval) : Fin 3 → AnalyticPiece (quadraticSlide I) :=
  Fin.cons (quadraticZeroPiece I) (quadraticBandPiece I)

/-- A concrete compatible cover with three retained cells and no
exceptional centre. It needs no abstract tame/cell input. -/
def quadraticCells (I : Interval) :
    RegularCellCover (quadraticSlide I) (fun _ _ => True) {p | p.2 0 ≠ 0} where
  count := 3
  piece := quadraticCellPiece I
  exceptional := ∅
  closed_exceptional := isClosed_empty
  null_exceptional := measure_empty
  cover := by
    intro p hp
    by_cases hz : p.2 0 = 0
    · refine Or.inr ⟨0, (p.1, 0), ?_, ?_⟩
      · have haux : p.2 = 0 := by ext i; fin_cases i; exact hz
        change (p.1, (0 : Aux 0)) ∈ ball (0 : Parameters 2 0) 1
        have hp' : ‖p.1‖ < 1 := by
          simpa [quadraticSlide, haux, mem_ball, dist_eq_norm, Prod.norm_def] using hp
        simpa only [mem_ball, dist_zero_right, Prod.norm_def, norm_zero,
          max_eq_left (norm_nonneg _)] using hp'
      · change (p.1, (0 : Aux 1)) = p
        refine Prod.ext (by rfl) ?_
        ext i
        fin_cases i
        exact hz.symm
    · by_cases hpos : 0 < p.2 0
      · exact Or.inr ⟨1, p, ⟨hp, hpos⟩, rfl⟩
      · exact Or.inr ⟨2, p, ⟨hp, lt_of_le_of_ne (le_of_not_gt hpos) hz⟩, rfl⟩
  disjoint := by
    intro i j hij
    apply disjoint_left.mpr
    rintro p ⟨q, hq, hqp⟩ ⟨r, hr, hrp⟩
    have hsign (i : Fin 3) (q : Parameters 2 (quadraticCellPiece I i).dim)
        (hq : q ∈ (quadraticCellPiece I i).family.W) :
        if i = 0 then ((quadraticCellPiece I i).embed q).2 0 = 0
        else if i = 1 then 0 < ((quadraticCellPiece I i).embed q).2 0
        else ((quadraticCellPiece I i).embed q).2 0 < 0 := by
      fin_cases i
      · rfl
      · exact hq.2
      · exact hq.2
    have hqsign := hsign i q hq
    have hrsign := hsign j r hr
    rw [hqp] at hqsign
    rw [hrp] at hrsign
    fin_cases i <;> fin_cases j <;> simp_all <;> linarith
  tame_children := fun _ => trivial
  lower_or_regular := by
    intro i
    fin_cases i
    · exact Or.inl (show 0 < 1 by omega)
    · refine Or.inr ⟨?_, ?_⟩
      · rintro _ ⟨p, hp, rfl⟩
        exact ne_of_gt hp.2
      · intro q _
        change Function.Surjective (fderiv ℝ (id : Parameters 2 1 → Parameters 2 1) q)
        simpa using (Function.surjective_id : Function.Surjective (id : Parameters 2 1 → Parameters 2 1))
    · refine Or.inr ⟨?_, ?_⟩
      · rintro _ ⟨p, hp, rfl⟩
        exact ne_of_lt hp.2
      · intro q _
        change Function.Surjective (fderiv ℝ (id : Parameters 2 1 → Parameters 2 1) q)
        simpa using (Function.surjective_id : Function.Surjective (id : Parameters 2 1 → Parameters 2 1))

abbrev quadraticCellStep (I : Interval) : RankCellStep (quadraticSlide I) (fun _ _ => True) :=
  (quadraticCells I).toRankCellStep (quadraticSlide_analytic I)
    (fun p hp => quadraticSlide_regular_ranks I p hp)

/-- The full finite decomposition of a variable-rank analytic family.
The singular cell has dimension zero and ranks (0,1); both open cells
have dimension one and ranks (1,1). -/
def quadraticDecomposition (I : Interval) : RankDecomposition (quadraticSlide I) :=
  (quadraticCellStep I).flatten (fun i =>
    RankDecomposition.single_proved (mp := if i.val = 0 then 0 else 1) (mc := 1)
      _ (quadraticCellPiece I i).open_domain
      (quadraticCellPiece I i).bounded_domain (quadraticCellPiece I i).connected_domain
      (quadraticCellPiece I i).analytic_family (by
        fin_cases i
        · change ConstantRanks (boundedHorizontal I) 0 1
          exact fun p _ => horizontal_ranks I p
        · change ConstantRanks ((quadraticSlide I).restrictTo (quadraticBand 0)) 1 1
          exact fun p hp => quadraticSlide_regular_ranks I p (ne_of_gt hp.2)
        · change ConstantRanks ((quadraticSlide I).restrictTo (quadraticBand 1)) 1 1
          exact fun p hp => quadraticSlide_regular_ranks I p (ne_of_lt hp.2)))

theorem quadraticDecomposition_exception_empty (I : Interval) :
    (quadraticDecomposition I).exceptional = ∅ := by
  change (∅ ∪ ⋃ _ : Fin 3, (∅ : Set (Base 2))) = ∅
  simp

theorem quadraticSlide_admitsNikodym (I : Interval) :
    (quadraticSlide I).AdmitsNikodym ∧ (quadraticSlide I).HasMassiveCurveReuse := by
  let P := quadraticBandPiece I 0
  have hr : ConstantRanks P.family 1 1 :=
    fun p hp => quadraticSlide_regular_ranks I p (ne_of_gt hp.2)
  have h := theorem_1_5_case_equal P.family P.connected_domain.nonempty
    P.open_domain P.analytic_family hr
  exact ⟨P.family.admitsNikodym_mono _ P.curves_mono h.1,
    P.family.hasMassiveCurveReuse_mono _ P.curves_mono h.2⟩

theorem quadraticDecomposition_partition (I : Interval) :
    (quadraticSlide I).W =
      (⋃ i, ((quadraticDecomposition I).piece i).toAnalyticPiece.image) ∪
        (quadraticDecomposition I).remainder ∧
      volume (closure (Prod.fst '' (quadraticDecomposition I).remainder)) = 0 :=
  ⟨(quadraticDecomposition I).partition,
    (quadraticDecomposition I).remainder_centers_closure_null⟩

end PlanarNikodym.Examples
