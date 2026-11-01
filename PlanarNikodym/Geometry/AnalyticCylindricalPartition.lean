import PlanarNikodym.Geometry.AnalyticBands

/-! A finite family of strictly ordered analytic graphs gives an actual disjoint
partition into graphs and open bands. Root collisions are excluded explicitly by
the strict ordering hypothesis. -/

noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym

variable {E : Type*} {N : ℕ}

/-- The graph of an actual function, restricted to the retained parameter set. -/
def analyticGraph (U : Set E) (f : E → ℝ) : Set (E × ℝ) :=
  {z | z.1 ∈ U ∧ z.2 = f z.1}

def analyticGraphMap (f : E → ℝ) (x : E) : E × ℝ := (x, f x)

theorem analyticGraphMap_image (U : Set E) (f : E → ℝ) :
    analyticGraphMap f '' U = analyticGraph U f := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, rfl⟩
  · intro hz
    exact ⟨z.1, hz.1, Prod.ext rfl hz.2.symm⟩

/-- The two endpoint cuts are included in `c`; its remaining cuts are the root graphs. -/
def analyticCylindricalCell (U : Set E) (c : Fin (N + 2) → E → ℝ) :
    (Fin N ⊕ Fin (N + 1)) → Set (E × ℝ)
  | Sum.inl i => analyticGraph U (c i.castSucc.succ)
  | Sum.inr i => analyticBand U (c i.castSucc) (c i.succ)

/-- Adjoin the fixed lower and upper boundaries to the actual root functions. -/
def analyticRootCuts (A B : ℝ) (ρ : Fin N → E → ℝ) : Fin (N + 2) → E → ℝ :=
  Fin.cases (fun _ => A) (Fin.lastCases (fun _ => B) ρ)

@[simp] theorem analyticRootCuts_zero (A B : ℝ) (ρ : Fin N → E → ℝ) :
    analyticRootCuts A B ρ 0 = fun _ => A := rfl

@[simp] theorem analyticRootCuts_last (A B : ℝ) (ρ : Fin N → E → ℝ) :
    analyticRootCuts A B ρ (Fin.last (N + 1)) = fun _ => B := by
  simp [analyticRootCuts, ← Fin.succ_last]

@[simp] theorem analyticRootCuts_interior (A B : ℝ) (ρ : Fin N → E → ℝ) (i : Fin N) :
    analyticRootCuts A B ρ i.castSucc.succ = ρ i := by
  simp [analyticRootCuts]

theorem strictMono_analyticRootCuts {U : Set E} (A B : ℝ) (ρ : Fin N → E → ℝ)
    (hAB : A < B) (hρ : ∀ x ∈ U, StrictMono (fun i => ρ i x))
    (hb : ∀ x ∈ U, ∀ i, ρ i x ∈ Ioo A B) :
    ∀ x ∈ U, StrictMono (fun i => analyticRootCuts A B ρ i x) := by
  intro x hx i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact False.elim (lt_irrefl _ hij)
    | succ j =>
      cases j using Fin.lastCases with
      | last => simpa only [Fin.succ_last, analyticRootCuts_zero,
          analyticRootCuts_last] using hAB
      | cast i => simpa [analyticRootCuts] using (hb x hx i).1
  | succ i =>
    cases j using Fin.cases with
    | zero => exact False.elim (Fin.not_lt_zero _ hij)
    | succ j =>
      cases i using Fin.lastCases with
      | last => exact False.elim (not_lt_of_ge (Fin.le_last _) hij)
      | cast i =>
        cases j using Fin.lastCases with
        | last => simpa only [Fin.succ_last, analyticRootCuts_interior,
            analyticRootCuts_last] using (hb x hx i).2
        | cast j =>
          simpa only [analyticRootCuts_interior] using hρ x hx (by simpa using hij)

theorem card_analyticCylindricalCellIndex :
    Fintype.card (Fin N ⊕ Fin (N + 1)) = 2 * N + 1 := by
  simp
  omega

/-- Every point strictly between the extreme cuts is on an interior cut or strictly
between two adjacent cuts. This includes the case with no interior cuts. -/
theorem ordered_cuts_cover {N : ℕ} (c : Fin (N + 2) → ℝ) (hc : StrictMono c)
    {t : ℝ} (hl : c 0 < t) (hu : t < c (Fin.last (N + 1))) :
    (∃ i : Fin N, t = c i.castSucc.succ) ∨
      ∃ i : Fin (N + 1), c i.castSucc < t ∧ t < c i.succ := by
  induction N with
  | zero => exact Or.inr ⟨0, hl, hu⟩
  | succ n ih =>
    let c' : Fin (n + 2) → ℝ := fun i => c i.castSucc
    have hc' : StrictMono c' := fun i j hij => hc (by exact hij)
    rcases lt_trichotomy t (c (Fin.last (n + 1)).castSucc) with ht | ht | ht
    · rcases ih c' hc' hl ht with ⟨i, hi⟩ | ⟨i, hil, hiu⟩
      · exact Or.inl ⟨i.castSucc, hi⟩
      · exact Or.inr ⟨i.castSucc, hil, hiu⟩
    · exact Or.inl ⟨Fin.last n, ht⟩
    · exact Or.inr ⟨Fin.last (n + 1), ht, hu⟩

theorem mem_analyticCylindricalCell_fst {U : Set E}
    {c : Fin (N + 2) → E → ℝ} {i : Fin N ⊕ Fin (N + 1)} {z : E × ℝ}
    (hz : z ∈ analyticCylindricalCell U c i) : z.1 ∈ U := by
  cases i <;> exact hz.1

theorem analyticCylindricalCell_subset {U : Set E}
    (c : Fin (N + 2) → E → ℝ)
    (hc : ∀ x ∈ U, StrictMono (fun i => c i x))
    (i : Fin N ⊕ Fin (N + 1)) :
    analyticCylindricalCell U c i ⊆ analyticBand U (c 0) (c (Fin.last (N + 1))) := by
  intro z hz
  have hx := mem_analyticCylindricalCell_fst hz
  refine ⟨hx, ?_, ?_⟩
  · cases i with
    | inl i =>
      rw [hz.2]
      exact hc z.1 hx (by simp)
    | inr i =>
      exact lt_of_le_of_lt ((hc z.1 hx).monotone (Fin.zero_le _)) hz.2.1
  · cases i with
    | inl i =>
      rw [hz.2]
      exact hc z.1 hx (by change (i : ℕ) + 1 < N + 1; omega)
    | inr i =>
      exact lt_of_lt_of_le hz.2.2 ((hc z.1 hx).monotone (Fin.le_last _))

theorem iUnion_analyticCylindricalCell {U : Set E}
    (c : Fin (N + 2) → E → ℝ)
    (hc : ∀ x ∈ U, StrictMono (fun i => c i x)) :
    (⋃ i, analyticCylindricalCell U c i) =
      analyticBand U (c 0) (c (Fin.last (N + 1))) := by
  apply Subset.antisymm
  · exact iUnion_subset (analyticCylindricalCell_subset c hc)
  · intro z hz
    rcases ordered_cuts_cover (fun i => c i z.1) (hc z.1 hz.1) hz.2.1 hz.2.2 with
      ⟨i, hi⟩ | ⟨i, hil, hiu⟩
    · exact mem_iUnion.mpr ⟨Sum.inl i, hz.1, hi⟩
    · exact mem_iUnion.mpr ⟨Sum.inr i, hz.1, hil, hiu⟩

theorem analyticCylindricalCell_index_eq {U : Set E}
    {c : Fin (N + 2) → E → ℝ}
    (hc : ∀ x ∈ U, StrictMono (fun i => c i x))
    {i j : Fin N ⊕ Fin (N + 1)} {z : E × ℝ}
    (hi : z ∈ analyticCylindricalCell U c i)
    (hj : z ∈ analyticCylindricalCell U c j) : i = j := by
  have hm := hc z.1 (mem_analyticCylindricalCell_fst hi)
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hh := hm.injective (hi.2.symm.trans hj.2)
      have hij : i = j := Fin.ext (by
        have hv := congrArg Fin.val hh
        simpa only [Fin.val_succ, Fin.val_castSucc, Nat.add_right_cancel_iff] using hv)
      exact congrArg Sum.inl hij
    | inr j =>
      have h₁ := hm.lt_iff_lt.mp (hj.2.1.trans_eq hi.2)
      have h₂ := hm.lt_iff_lt.mp (hi.2.symm.trans_lt hj.2.2)
      have : (j : ℕ) < (i : ℕ) + 1 ∧ (i : ℕ) + 1 < (j : ℕ) + 1 := ⟨h₁, h₂⟩
      omega
  | inr i =>
    cases j with
    | inl j =>
      have h₁ := hm.lt_iff_lt.mp (hi.2.1.trans_eq hj.2)
      have h₂ := hm.lt_iff_lt.mp (hj.2.symm.trans_lt hi.2.2)
      have : (i : ℕ) < (j : ℕ) + 1 ∧ (j : ℕ) + 1 < (i : ℕ) + 1 := ⟨h₁, h₂⟩
      omega
    | inr j =>
      have hij : i = j := by
        apply le_antisymm
        · by_contra hn
          have hjile : j.succ ≤ i.castSucc := by
            change (j : ℕ) + 1 ≤ (i : ℕ)
            have : j < i := lt_of_not_ge hn
            omega
          have hh := (hm.monotone hjile).trans_lt hi.2.1
          exact (lt_irrefl z.2) (hj.2.2.trans hh)
        · by_contra hn
          have hijle : i.succ ≤ j.castSucc := by
            change (i : ℕ) + 1 ≤ (j : ℕ)
            have : i < j := lt_of_not_ge hn
            omega
          have hh := (hm.monotone hijle).trans_lt hj.2.1
          exact (lt_irrefl z.2) (hi.2.2.trans hh)
      exact congrArg Sum.inr hij

theorem pairwiseDisjoint_analyticCylindricalCell {U : Set E}
    (c : Fin (N + 2) → E → ℝ)
    (hc : ∀ x ∈ U, StrictMono (fun i => c i x)) :
    Pairwise (fun i j => Disjoint (analyticCylindricalCell U c i)
      (analyticCylindricalCell U c j)) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro z hzi hzj
  exact hij (analyticCylindricalCell_index_eq hc hzi hzj)

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem analyticOnNhd_analyticRootCuts {U : Set E} (A B : ℝ) (ρ : Fin N → E → ℝ)
    (hρ : ∀ i, AnalyticOnNhd ℝ (ρ i) U) :
    ∀ i, AnalyticOnNhd ℝ (analyticRootCuts A B ρ i) U := by
  intro i
  cases i using Fin.cases with
  | zero => exact fun _ _ => analyticAt_const
  | succ i =>
    cases i using Fin.lastCases with
    | last => simpa only [Fin.succ_last, analyticRootCuts_last] using
        (show AnalyticOnNhd ℝ (fun _ : E => B) U from fun _ _ => analyticAt_const)
    | cast i => simpa [analyticRootCuts] using hρ i

theorem analyticOnNhd_analyticGraphMap {U : Set E} {f : E → ℝ}
    (hf : AnalyticOnNhd ℝ f U) : AnalyticOnNhd ℝ (analyticGraphMap f) U :=
  fun x hx => analyticAt_id.prod (hf x hx)

/-- The actual graph parameterization has the continuous inverse given by projection. -/
def analyticGraphHomeomorph {U : Set E} (f : E → ℝ)
    (hf : AnalyticOnNhd ℝ f U) : U ≃ₜ analyticGraph U f where
  toFun x := ⟨analyticGraphMap f x, x.2, rfl⟩
  invFun z := ⟨z.1.1, z.2.1⟩
  left_inv _ := rfl
  right_inv z := Subtype.ext (Prod.ext rfl z.2.2.symm)
  continuous_toFun :=
    (analyticOnNhd_analyticGraphMap hf).continuousOn.restrict.subtype_mk _
  continuous_invFun := (continuous_fst.comp continuous_subtype_val).subtype_mk _

theorem isConnected_analyticGraph {U : Set E} {f : E → ℝ}
    (hU : IsConnected U) (hf : AnalyticOnNhd ℝ f U) :
    IsConnected (analyticGraph U f) := by
  rw [← analyticGraphMap_image]
  exact hU.image (analyticGraphMap f) (analyticOnNhd_analyticGraphMap hf).continuousOn

theorem isConnected_analyticCylindricalCell {U : Set E}
    (c : Fin (N + 2) → E → ℝ) (hU : IsConnected U)
    (ha : ∀ i, AnalyticOnNhd ℝ (c i) U)
    (hc : ∀ x ∈ U, StrictMono (fun i => c i x))
    (i : Fin N ⊕ Fin (N + 1)) :
    IsConnected (analyticCylindricalCell U c i) := by
  cases i with
  | inl i => exact isConnected_analyticGraph hU (ha _)
  | inr i =>
    exact isConnected_analyticBand hU (ha _) (ha _) (fun x hx => hc x hx (by simp))

theorem injective_analyticCylindricalCell {U : Set E}
    (c : Fin (N + 2) → E → ℝ) (hU : IsConnected U)
    (ha : ∀ i, AnalyticOnNhd ℝ (c i) U)
    (hc : ∀ x ∈ U, StrictMono (fun i => c i x)) :
    Function.Injective (analyticCylindricalCell U c) := by
  intro i j hij
  obtain ⟨z, hz⟩ := (isConnected_analyticCylindricalCell c hU ha hc i).nonempty
  exact analyticCylindricalCell_index_eq hc hz (hij ▸ hz)

theorem ncard_range_analyticCylindricalCell {U : Set E}
    (c : Fin (N + 2) → E → ℝ) (hU : IsConnected U)
    (ha : ∀ i, AnalyticOnNhd ℝ (c i) U)
    (hc : ∀ x ∈ U, StrictMono (fun i => c i x)) :
    (Set.range (analyticCylindricalCell U c)).ncard = 2 * N + 1 := by
  rw [Set.ncard_range_of_injective (injective_analyticCylindricalCell c hU ha hc),
    Nat.card_eq_fintype_card, card_analyticCylindricalCellIndex]

/-- A continuous nonvanishing real function has one strict sign on a connected set. -/
theorem sign_constant_on_connected_of_ne_zero {X : Type*} [TopologicalSpace X]
    {S : Set X} (hS : IsConnected S) (f : X → ℝ) (hf : ContinuousOn f S)
    (hn : ∀ z ∈ S, f z ≠ 0) :
    (∀ z ∈ S, f z < 0) ∨ (∀ z ∈ S, 0 < f z) := by
  obtain ⟨x, hx⟩ := hS.nonempty
  rcases lt_or_gt_of_ne (hn x hx) with hneg | hpos
  · left
    intro y hy
    by_contra h
    obtain ⟨z, hz, hz₀⟩ :=
      hS.isPreconnected.intermediate_value hx hy hf ⟨hneg.le, le_of_not_gt h⟩
    exact hn z hz hz₀
  · right
    intro y hy
    by_contra h
    obtain ⟨z, hz, hz₀⟩ :=
      hS.isPreconnected.intermediate_value hy hx hf ⟨le_of_not_gt h, hpos.le⟩
    exact hn z hz hz₀

/-- If all zeros lie on the listed root graphs, each intervening band has a strict
constant sign. This does not assert anything about signs on the graphs themselves. -/
theorem analyticCylindricalBand_sign_constant {U : Set E}
    (c : Fin (N + 2) → E → ℝ) (hU : IsConnected U)
    (ha : ∀ i, AnalyticOnNhd ℝ (c i) U)
    (hc : ∀ x ∈ U, StrictMono (fun i => c i x))
    (f : E × ℝ → ℝ)
    (hf : ContinuousOn f (analyticBand U (c 0) (c (Fin.last (N + 1)))))
    (hz : ∀ z ∈ analyticBand U (c 0) (c (Fin.last (N + 1))), f z = 0 →
      ∃ j : Fin N, z.2 = c j.castSucc.succ z.1)
    (i : Fin (N + 1)) :
    (∀ z ∈ analyticCylindricalCell U c (Sum.inr i), f z < 0) ∨
      (∀ z ∈ analyticCylindricalCell U c (Sum.inr i), 0 < f z) := by
  apply sign_constant_on_connected_of_ne_zero
    (isConnected_analyticCylindricalCell c hU ha hc (Sum.inr i)) f
    (hf.mono (analyticCylindricalCell_subset c hc (Sum.inr i)))
  intro z hzi hzf
  obtain ⟨j, hj⟩ := hz z (analyticCylindricalCell_subset c hc _ hzi) hzf
  have hzg : z ∈ analyticCylindricalCell U c (Sum.inl j) :=
    ⟨mem_analyticCylindricalCell_fst hzi, hj⟩
  have hbad := analyticCylindricalCell_index_eq hc hzi hzg
  cases hbad

/-- A whole family is sign invariant on every cell once graph compatibility is
provided. Compatibility says separately for each function and graph that the function
is identically zero or nowhere zero there; it is not inferred from the union of zeros. -/
theorem analyticCylindricalCell_family_sign_constant {ι : Type*} {U : Set E}
    (c : Fin (N + 2) → E → ℝ) (hU : IsConnected U)
    (ha : ∀ i, AnalyticOnNhd ℝ (c i) U)
    (hc : ∀ x ∈ U, StrictMono (fun i => c i x))
    (f : ι → E × ℝ → ℝ)
    (hf : ∀ j, ContinuousOn (f j) (analyticBand U (c 0) (c (Fin.last (N + 1)))))
    (hz : ∀ j z, z ∈ analyticBand U (c 0) (c (Fin.last (N + 1))) → f j z = 0 →
      ∃ l : Fin N, z.2 = c l.castSucc.succ z.1)
    (hg : ∀ j (l : Fin N),
      (∀ z ∈ analyticCylindricalCell U c (Sum.inl l), f j z = 0) ∨
      (∀ z ∈ analyticCylindricalCell U c (Sum.inl l), f j z ≠ 0)) :
    ∀ (i : Fin N ⊕ Fin (N + 1)) j,
      (∀ z ∈ analyticCylindricalCell U c i, f j z < 0) ∨
      (∀ z ∈ analyticCylindricalCell U c i, f j z = 0) ∨
      (∀ z ∈ analyticCylindricalCell U c i, 0 < f j z) := by
  intro i j
  cases i with
  | inl l =>
    rcases hg j l with hzero | hnonzero
    · exact Or.inr (Or.inl hzero)
    · rcases sign_constant_on_connected_of_ne_zero
        (isConnected_analyticCylindricalCell c hU ha hc (Sum.inl l)) (f j)
        ((hf j).mono (analyticCylindricalCell_subset c hc (Sum.inl l))) hnonzero with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  | inr l =>
    rcases analyticCylindricalBand_sign_constant c hU ha hc (f j) (hf j) (hz j) l with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

/-- The concrete `2N+1` cells from ordered root functions cover exactly the fixed
cylinder, are pairwise disjoint, and are all connected. Graph and band coordinates
are supplied by `analyticGraphHomeomorph` and `analyticBandHomeomorph`. -/
theorem analytic_ordered_root_partition {U : Set E}
    (A B : ℝ) (ρ : Fin N → E → ℝ) (hAB : A < B) (hU : IsConnected U)
    (ha : ∀ i, AnalyticOnNhd ℝ (ρ i) U)
    (hρ : ∀ x ∈ U, StrictMono (fun i => ρ i x))
    (hb : ∀ x ∈ U, ∀ i, ρ i x ∈ Ioo A B) :
    (⋃ i, analyticCylindricalCell U (analyticRootCuts A B ρ) i) = U ×ˢ Ioo A B ∧
    Pairwise (fun i j =>
      Disjoint (analyticCylindricalCell U (analyticRootCuts A B ρ) i)
        (analyticCylindricalCell U (analyticRootCuts A B ρ) j)) ∧
    ∀ i, IsConnected (analyticCylindricalCell U (analyticRootCuts A B ρ) i) := by
  have hc := strictMono_analyticRootCuts A B ρ hAB hρ hb
  refine ⟨?_, pairwiseDisjoint_analyticCylindricalCell _ hc, ?_⟩
  · rw [iUnion_analyticCylindricalCell _ hc]
    simp only [analyticRootCuts_zero, analyticRootCuts_last]
    rfl
  · exact isConnected_analyticCylindricalCell _ hU
      (analyticOnNhd_analyticRootCuts A B ρ ha) hc

/-- When the given graphs are exactly the zero set, the function vanishes on every
graph and has a strict constant sign on each band. -/
theorem analytic_ordered_root_sign_partition {U : Set E}
    (A B : ℝ) (ρ : Fin N → E → ℝ) (hAB : A < B) (hU : IsConnected U)
    (ha : ∀ i, AnalyticOnNhd ℝ (ρ i) U)
    (hρ : ∀ x ∈ U, StrictMono (fun i => ρ i x))
    (hb : ∀ x ∈ U, ∀ i, ρ i x ∈ Ioo A B)
    (f : E × ℝ → ℝ) (hf : ContinuousOn f (U ×ˢ Ioo A B))
    (hz : ∀ x ∈ U, ∀ t ∈ Ioo A B, f (x, t) = 0 ↔ ∃ i, t = ρ i x) :
    (∀ (i : Fin N) z,
      z ∈ analyticCylindricalCell U (analyticRootCuts A B ρ) (Sum.inl i) → f z = 0) ∧
    (∀ i : Fin (N + 1),
      (∀ z ∈ analyticCylindricalCell U (analyticRootCuts A B ρ) (Sum.inr i), f z < 0) ∨
      (∀ z ∈ analyticCylindricalCell U (analyticRootCuts A B ρ) (Sum.inr i), 0 < f z)) := by
  have hc := strictMono_analyticRootCuts A B ρ hAB hρ hb
  have hca := analyticOnNhd_analyticRootCuts A B ρ ha
  have hband : analyticBand U (analyticRootCuts A B ρ 0)
      (analyticRootCuts A B ρ (Fin.last (N + 1))) = U ×ˢ Ioo A B := by
    simp only [analyticRootCuts_zero, analyticRootCuts_last]
    rfl
  constructor
  · intro i z hzi
    have hm : z ∈ U ×ˢ Ioo A B := by
      rw [← hband]
      exact analyticCylindricalCell_subset _ hc _ hzi
    apply (hz z.1 hm.1 z.2 hm.2).mpr
    exact ⟨i, by simpa only [analyticRootCuts_interior] using hzi.2⟩
  · intro i
    apply analyticCylindricalBand_sign_constant _ hU hca hc f
      (hband.symm ▸ hf)
    intro z hzm hzf
    rw [hband] at hzm
    obtain ⟨j, hj⟩ := (hz z.1 hzm.1 z.2 hzm.2).mp hzf
    exact ⟨j, by simpa only [analyticRootCuts_interior] using hj⟩

end PlanarNikodym
