import PlanarNikodym.Geometry.AnalyticPolynomialRootBranches

/-! Globally ordered analytic real roots on the open loci of fixed root count.
The global branches are the actual sorted root sets. Local complete analytic
atlases agree with them by uniqueness of increasing enumerations. -/

noncomputable section
open Set Filter Polynomial
open scoped Topology
namespace PlanarNikodym

/-- The number of distinct actual real roots of a monic coefficient vector. -/
def polynomialRealRootCount {m : ℕ} (a : Fin m → ℝ) : ℕ :=
  ((weierstrassPolynomial a).rootSet ℝ).ncard

/-- The simple-root locus of a fixed actual real root count. -/
def polynomialSimpleRootCountDomain {E : Type*} {m : ℕ}
    (a : E → Fin m → ℝ) (V : Set E) (n : ℕ) : Set E :=
  {x | x ∈ V ∧ weierstrassCollisionDet (a x) ≠ 0 ∧ polynomialRealRootCount (a x) = n}

theorem polynomialRealRootCount_le {m : ℕ} (a : Fin m → ℝ) :
    polynomialRealRootCount a ≤ m := by
  simpa only [polynomialRealRootCount, weierstrassPolynomial_natDegree] using
    (weierstrassPolynomial a).ncard_rootSet_le ℝ

theorem mem_weierstrassPolynomial_real_rootSet {m : ℕ} (a : Fin m → ℝ) (t : ℝ) :
    t ∈ (weierstrassPolynomial a).rootSet ℝ ↔ (weierstrassPolynomial a).eval t = 0 := by
  rw [(weierstrassPolynomial_monic a).mem_rootSet]
  simp [Polynomial.aeval_def]

/-- Complete strictly increasing root lists have the actual root count. -/
theorem polynomialRealRootCount_eq_of_ordered_roots
    {m n : ℕ} (a : Fin m → ℝ) (r : Fin n → ℝ) (hr : StrictMono r)
    (hroots : ∀ t, (weierstrassPolynomial a).eval t = 0 ↔ ∃ i, t = r i) :
    polynomialRealRootCount a = n := by
  have he : (weierstrassPolynomial a).rootSet ℝ = Set.range r := by
    ext t
    rw [mem_weierstrassPolynomial_real_rootSet]
    simpa only [Set.mem_range, eq_comm] using hroots t
  rw [polynomialRealRootCount, he, Set.ncard_range_of_injective hr.injective]
  simp

/-- The sorted `i`-th actual root when the root count is `n`, extended by zero
outside that count. This global definition makes no analytic choice of a local
chart and permits the fixed-count domain to be empty or disconnected. -/
def orderedPolynomialRealRoot {m : ℕ} (a : Fin m → ℝ) (n : ℕ) (i : Fin n) : ℝ := by
  classical
  exact if h : polynomialRealRootCount a = n then
    ((weierstrassPolynomial a).rootSet_finite ℝ).toFinset.orderEmbOfFin
      ((Set.ncard_eq_toFinset_card _ ((weierstrassPolynomial a).rootSet_finite ℝ)).symm.trans h) i
  else 0

theorem orderedPolynomialRealRoot_spec {m : ℕ} (a : Fin m → ℝ) (n : ℕ)
    (hn : polynomialRealRootCount a = n) :
    StrictMono (orderedPolynomialRealRoot a n) ∧
      ∀ t, (weierstrassPolynomial a).eval t = 0 ↔
        ∃ i, t = orderedPolynomialRealRoot a n i := by
  classical
  let S := ((weierstrassPolynomial a).rootSet_finite ℝ).toFinset
  have hcard : S.card = n :=
    (Set.ncard_eq_toFinset_card _ ((weierstrassPolynomial a).rootSet_finite ℝ)).symm.trans hn
  have he : orderedPolynomialRealRoot a n = S.orderEmbOfFin hcard := by
    funext i
    simp only [orderedPolynomialRealRoot, dif_pos hn]
    rfl
  rw [he]
  refine ⟨(S.orderEmbOfFin hcard).strictMono, ?_⟩
  intro t
  rw [← mem_weierstrassPolynomial_real_rootSet]
  have hrange : Set.range (S.orderEmbOfFin hcard) = (weierstrassPolynomial a).rootSet ℝ := by
    rw [Finset.range_orderEmbOfFin]
    exact Set.Finite.coe_toFinset _
  rw [← hrange]
  simp only [Set.mem_range, eq_comm]

/-- An actual root-count equation is equivalent to the finite ordered-list
formula. This equivalence does not require simple roots and can be used to
transport genuine definability of that finite formula. -/
theorem polynomialRealRootCount_eq_iff_exists_ordered_roots
    {m : ℕ} (a : Fin m → ℝ) (n : ℕ) :
    polynomialRealRootCount a = n ↔
      ∃ r : Fin n → ℝ, StrictMono r ∧
        ∀ t, (weierstrassPolynomial a).eval t = 0 ↔ ∃ i, t = r i := by
  constructor
  · intro h
    exact ⟨orderedPolynomialRealRoot a n, orderedPolynomialRealRoot_spec a n h⟩
  · rintro ⟨r, hr, hroots⟩
    exact polynomialRealRootCount_eq_of_ordered_roots a r hr hroots

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The local complete root atlas fixes the root count on an actual ball in
its nonzero-discriminant locus. Its root list has exactly the specified index. -/
theorem exists_local_polynomial_roots_of_fixed_count
    {m n : ℕ} (a : E → Fin m → ℝ) (V : Set E) (hV : IsOpen V)
    (ha : AnalyticOnNhd ℝ a V) (x : E)
    (hx : x ∈ polynomialSimpleRootCountDomain a V n) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball x ε ⊆ polynomialSimpleRootCountDomain a V n ∧
      ∃ ρ : Fin n → E → ℝ,
        (∀ i, AnalyticOnNhd ℝ (ρ i) (Metric.ball x ε)) ∧
        (∀ y ∈ Metric.ball x ε, StrictMono (fun i => ρ i y)) ∧
        ∀ y ∈ Metric.ball x ε, ∀ t,
          (weierstrassPolynomial (a y)).eval t = 0 ↔ ∃ i, t = ρ i y := by
  obtain ⟨k, ε₀, R, hε₀, hR, ρ, ha₀, hρ, hmono, hbound, hroots⟩ :=
    exists_ordered_analytic_polynomial_root_branches_of_collisionDet_ne_zero
      a x (ha x hx.1) hx.2.1
  have hkn : k = n :=
    (polynomialRealRootCount_eq_of_ordered_roots (a x) (fun i => ρ i x)
      (hmono x (Metric.mem_ball_self hε₀)) (hroots x (Metric.mem_ball_self hε₀))).symm.trans hx.2.2
  subst k
  have hnear : {y | y ∈ V ∧ weierstrassCollisionDet (a y) ≠ 0 ∧
      y ∈ Metric.ball x ε₀} ∈ 𝓝 x := by
    filter_upwards [hV.mem_nhds hx.1,
      (analyticAt_weierstrassCollisionDet a x (ha x hx.1)).continuousAt.eventually_ne hx.2.1,
      Metric.ball_mem_nhds x hε₀] with y hy hdy hby
    exact ⟨hy, hdy, hby⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨ε, hε, ?_, ρ, ?_, ?_, ?_⟩
  · intro y hy
    exact ⟨(hball hy).1, (hball hy).2.1,
      polynomialRealRootCount_eq_of_ordered_roots (a y) (fun i => ρ i y)
        (hmono y (hball hy).2.2) (hroots y (hball hy).2.2)⟩
  · intro i y hy
    exact hρ i y (hball hy).2.2
  · intro y hy
    exact hmono y (hball hy).2.2
  · intro y hy
    exact hroots y (hball hy).2.2

/-- Each fixed-count simple-root parameter locus is actually open. -/
theorem isOpen_polynomialSimpleRootCountDomain
    {m : ℕ} (a : E → Fin m → ℝ) (V : Set E) (hV : IsOpen V)
    (ha : AnalyticOnNhd ℝ a V) (n : ℕ) :
    IsOpen (polynomialSimpleRootCountDomain a V n) := by
  rw [Metric.isOpen_iff]
  intro x hx
  obtain ⟨ε, hε, hb, _⟩ := exists_local_polynomial_roots_of_fixed_count a V hV ha x hx
  exact ⟨ε, hε, hb⟩

/-- The actual sorted roots are analytic throughout the entire fixed-count
simple-root locus. Uniqueness of ordered root lists glues all local charts. -/
theorem analyticOnNhd_orderedPolynomialRealRoot
    {m : ℕ} (a : E → Fin m → ℝ) (V : Set E) (hV : IsOpen V)
    (ha : AnalyticOnNhd ℝ a V) (n : ℕ) (i : Fin n) :
    AnalyticOnNhd ℝ (fun x => orderedPolynomialRealRoot (a x) n i)
      (polynomialSimpleRootCountDomain a V n) := by
  intro x hx
  obtain ⟨ε, hε, hB, ρ, hρ, hm, hr⟩ :=
    exists_local_polynomial_roots_of_fixed_count a V hV ha x hx
  apply (hρ i x (Metric.mem_ball_self hε)).congr
  filter_upwards [Metric.ball_mem_nhds x hε] with y hy
  obtain ⟨hmon, hroot⟩ := orderedPolynomialRealRoot_spec (a y) n (hB hy).2.2
  have he : (fun j => ρ j y) = orderedPolynomialRealRoot (a y) n := by
    apply ((hm y hy).range_inj hmon).mp
    ext t
    simp only [Set.mem_range]
    constructor
    · rintro ⟨j, rfl⟩
      obtain ⟨l, hl⟩ := (hroot (ρ j y)).mp ((hr y hy (ρ j y)).mpr ⟨j, rfl⟩)
      exact ⟨l, hl.symm⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨l, hl⟩ := (hr y hy (orderedPolynomialRealRoot (a y) n j)).mp
        ((hroot _).mpr ⟨j, rfl⟩)
      exact ⟨l, hl.symm⟩
  exact congrFun he i

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
/-- The finitely many root-count loci are disjoint and cover the complete
simple-root domain, including the locus of no real roots. -/
theorem polynomialSimpleRootCountDomain_finite_partition
    {m : ℕ} (a : E → Fin m → ℝ) (V : Set E) :
    (⋃ n : Fin (m + 1), polynomialSimpleRootCountDomain a V n) =
      {x | x ∈ V ∧ weierstrassCollisionDet (a x) ≠ 0} ∧
    Pairwise (fun i j : Fin (m + 1) => Disjoint
      (polynomialSimpleRootCountDomain a V i) (polynomialSimpleRootCountDomain a V j)) := by
  constructor
  · ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      exact ⟨hn.1, hn.2.1⟩
    · rintro ⟨hx, hd⟩
      exact mem_iUnion.mpr ⟨⟨polynomialRealRootCount (a x),
        Nat.lt_succ_of_le (polynomialRealRootCount_le (a x))⟩, hx, hd, rfl⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    exact hij (Fin.ext (hi.2.2.symm.trans hj.2.2))

/-- Global finite ordered analytic root branches on every fixed-count locus,
constructed from the original analytic coefficients and actual discriminant. -/
theorem exists_global_ordered_analytic_polynomial_roots
    {m : ℕ} (a : E → Fin m → ℝ) (V : Set E) (hV : IsOpen V)
    (ha : AnalyticOnNhd ℝ a V) (n : ℕ) :
    IsOpen (polynomialSimpleRootCountDomain a V n) ∧
    ∃ ρ : Fin n → E → ℝ,
      (∀ i, AnalyticOnNhd ℝ (ρ i) (polynomialSimpleRootCountDomain a V n)) ∧
      (∀ x ∈ polynomialSimpleRootCountDomain a V n, StrictMono (fun i => ρ i x)) ∧
      ∀ x ∈ polynomialSimpleRootCountDomain a V n, ∀ t,
        (weierstrassPolynomial (a x)).eval t = 0 ↔ ∃ i, t = ρ i x := by
  refine ⟨isOpen_polynomialSimpleRootCountDomain a V hV ha n,
    (fun i x => orderedPolynomialRealRoot (a x) n i), ?_, ?_, ?_⟩
  · exact analyticOnNhd_orderedPolynomialRealRoot a V hV ha n
  · intro x hx
    exact (orderedPolynomialRealRoot_spec (a x) n hx.2.2).1
  · intro x hx
    exact (orderedPolynomialRealRoot_spec (a x) n hx.2.2).2

end PlanarNikodym
