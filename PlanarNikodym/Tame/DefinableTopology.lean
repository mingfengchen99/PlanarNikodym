import PlanarNikodym.Tame.DefinableMapOn

/-! Topological operations are expressed by actual finite first-order
quantifiers. These results use neither cell decomposition nor o-minimality. -/

noncomputable section
open Set Metric

namespace PlanarNikodym

theorem ranDefinable_exists_real {ι : Type*} [Finite ι]
    {P : (ι → ℝ) → ℝ → Prop}
    (hP : RanDefinable {w : Option ι → ℝ | P (w ∘ some) (w none)}) :
    RanDefinable {x | ∃ t, P x t} := by
  convert hP.image_comp some using 1
  ext x
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨(fun i => Option.elim i t x), ht, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w none, hw⟩

theorem ranDefinable_forall_real {ι : Type*} [Finite ι]
    {P : (ι → ℝ) → ℝ → Prop}
    (hP : RanDefinable {w : Option ι → ℝ | P (w ∘ some) (w none)}) :
    RanDefinable {x | ∀ t, P x t} := by
  have hnot : RanDefinable {w : Option ι → ℝ | ¬ P (w ∘ some) (w none)} := hP.compl
  simpa only [compl_setOf, not_exists, not_not] using
    (ranDefinable_exists_real (P := fun x t => ¬ P x t) hnot).compl

theorem ranDefinable_dist_lt {ι κ : Type*} [Fintype κ]
    {F G : (ι → ℝ) → (κ → ℝ)} {r : (ι → ℝ) → ℝ}
    (hF : RanDefinableMap F) (hG : RanDefinableMap G) (hr : RanDefinableFun r) :
    RanDefinable {x | 0 < r x ∧ dist (F x) (G x) < r x} := by
  have hcoord (i : κ) :
      RanDefinable {x | G x i - r x < F x i ∧ F x i < G x i + r x} :=
    (ranDefinable_lt (ranDefinableFun_sub (hG i) hr) (hF i)).inter
      (ranDefinable_lt (hF i) (ranDefinableFun_add (hG i) hr))
  convert (ranDefinable_lt (ranDefinableFun_const 0) hr).inter
    (Set.definable_iInter_of_finite hcoord) using 1
  ext x
  simp only [mem_setOf_eq, mem_inter_iff, mem_iInter]
  apply and_congr_right
  intro hx
  rw [dist_pi_lt_iff hx]
  apply forall_congr'
  intro i
  rw [Real.dist_eq, abs_lt]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- Euclidean closure is definable, using the metric of the actual finite
coordinate space (including the empty coordinate space). -/
theorem RanDefinable.closure {ι : Type*} [Fintype ι] {S : Set (ι → ℝ)}
    (hS : RanDefinable S) : RanDefinable (closure S) := by
  have hnear : RanDefinable {w : (Option ι ⊕ ι) → ℝ |
      w ∘ Sum.inr ∈ S ∧ 0 < w (.inl none) ∧
        dist (fun i => w (.inl (some i))) (w ∘ Sum.inr) < w (.inl none)} :=
    (hS.preimage_comp Sum.inr).inter
      (ranDefinable_dist_lt (F := fun w i => w (Sum.inl (some i)))
        (G := fun w i => w (Sum.inr i)) (r := fun w => w (Sum.inl none))
        (fun i => ranDefinableFun_coordinate (Sum.inl (some i)))
        (fun i => ranDefinableFun_coordinate (Sum.inr i))
        (ranDefinableFun_coordinate (Sum.inl none)))
  have hex := hnear.exists_of_finite
  have hpos : RanDefinable {w : Option ι → ℝ | 0 < w none} :=
    ranDefinable_lt (ranDefinableFun_const 0) (ranDefinableFun_coordinate none)
  have hall := ranDefinable_forall_real
    (P := fun x r => ¬ 0 < r ∨ ∃ y, y ∈ S ∧ 0 < r ∧ dist x y < r)
    (hpos.compl.union hex)
  convert hall using 1
  ext x
  simp only [Metric.mem_closure_iff, mem_setOf_eq]
  constructor
  · intro hx r
    by_cases hr : 0 < r
    · obtain ⟨y, hy, hd⟩ := hx r hr
      exact Or.inr ⟨y, hy, hr, hd⟩
    · exact Or.inl hr
  · intro hx r hr
    obtain h | ⟨y, hy, _, hd⟩ := hx r
    · exact (h hr).elim
    · exact ⟨y, hy, hd⟩

theorem RanDefinable.interior {ι : Type*} [Fintype ι] {S : Set (ι → ℝ)}
    (hS : RanDefinable S) : RanDefinable (interior S) := by
  rw [interior_eq_compl_closure_compl]
  exact (RanDefinable.closure hS.compl).compl

theorem RanDefinable.frontier {ι : Type*} [Fintype ι] {S : Set (ι → ℝ)}
    (hS : RanDefinable S) : RanDefinable (frontier S) :=
  (RanDefinable.closure hS).sdiff (RanDefinable.interior hS)

/-- Actual images under maps definable only on their source domain. -/
theorem ranDefinable_image_on {ι κ : Type*} [Finite ι] [Finite κ]
    {S : Set (ι → ℝ)} (hS : RanDefinable S) {F : (ι → ℝ) → (κ → ℝ)}
    (hF : ∀ i, RanDefinableOn (fun x => F x i) S) : RanDefinable (F '' S) := by
  have hgraph : RanDefinable {w : (κ ⊕ ι) → ℝ |
      w ∘ Sum.inr ∈ S ∧ ∀ i, F (w ∘ Sum.inr) i = w (.inl i)} := by
    have h (i : κ) := (hF i).preimage_comp
      (fun | none => Sum.inl i | some j => Sum.inr j)
    convert (hS.preimage_comp Sum.inr).inter
      (Set.definable_iInter_of_finite h) using 1
    ext w
    simp only [mem_inter_iff, mem_iInter, mem_setOf_eq,
      mem_preimage, Function.comp_def]
    exact and_congr_right fun hx => forall_congr' fun i =>
      ⟨fun he => ⟨hx, he⟩, fun he => he.2⟩
  convert hgraph.exists_of_finite using 1
  ext y
  simp only [mem_image, mem_setOf_eq, Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  exact exists_congr fun x => and_congr_right fun _ => funext_iff

end PlanarNikodym
