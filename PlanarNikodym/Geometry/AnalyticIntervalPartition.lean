import PlanarNikodym.Geometry.AnalyticZeros
import Mathlib.Topology.Order.IntermediateValue

/-! Finite sign partitions for an actual finite analytic family on a
compact real interval. The cuts are the zeroes of the nonzero functions.
Identically zero members are allowed and do not contribute cuts. -/
noncomputable section
open Set
namespace PlanarNikodym

/-- The three strict/zero comparison states, encoded by `0,1,2`. -/
def oneDimensionalSign (x : ℝ) : Fin 3 :=
  if x < 0 then 0 else if x = 0 then 1 else 2

@[simp] theorem oneDimensionalSign_eq_zero {x : ℝ} :
    oneDimensionalSign x = 0 ↔ x < 0 := by
  unfold oneDimensionalSign
  split_ifs <;> simp_all

@[simp] theorem oneDimensionalSign_eq_one {x : ℝ} :
    oneDimensionalSign x = 1 ↔ x = 0 := by
  unfold oneDimensionalSign
  split_ifs <;> simp_all
  grind

@[simp] theorem oneDimensionalSign_eq_two {x : ℝ} :
    oneDimensionalSign x = 2 ↔ 0 < x := by
  unfold oneDimensionalSign
  split_ifs <;> simp_all <;> grind

/-- A cell is an intersection of the compact interval with one specified
side, or the singleton, at each of finitely many actual cut points. -/
def analyticIntervalAtom (I : Interval) (S : Finset ℝ) (σ : S → Fin 3) : Set ℝ :=
  {x | x ∈ I.carrier ∧ ∀ z : S, oneDimensionalSign (x - z) = σ z}

theorem analyticIntervalAtom_subset (I : Interval) (S : Finset ℝ) (σ : S → Fin 3) :
    analyticIntervalAtom I S σ ⊆ I.carrier := fun _ hx => hx.1

theorem analyticIntervalAtom_ordConnected (I : Interval) (S : Finset ℝ)
    (σ : S → Fin 3) : (analyticIntervalAtom I S σ).OrdConnected := by
  refine ⟨?_⟩
  intro x hx y hy t ht
  refine ⟨⟨hx.1.1.trans ht.1, ht.2.trans hy.1.2⟩, ?_⟩
  intro z
  have hxz := hx.2 z
  have hyz := hy.2 z
  have hcases : σ z = 0 ∨ σ z = 1 ∨ σ z = 2 := by omega
  rcases hcases with h | h | h
  · rw [h] at hxz hyz ⊢
    rw [oneDimensionalSign_eq_zero] at hxz hyz ⊢
    linarith [ht.2]
  · rw [h] at hxz hyz ⊢
    rw [oneDimensionalSign_eq_one] at hxz hyz ⊢
    linarith [ht.1, ht.2]
  · rw [h] at hxz hyz ⊢
    rw [oneDimensionalSign_eq_two] at hxz hyz ⊢
    linarith [ht.1]

theorem analyticIntervalAtom_isPreconnected (I : Interval) (S : Finset ℝ)
    (σ : S → Fin 3) : IsPreconnected (analyticIntervalAtom I S σ) :=
  (analyticIntervalAtom_ordConnected I S σ).isPreconnected

theorem analyticIntervalAtom_pairwiseDisjoint (I : Interval) (S : Finset ℝ) :
    Pairwise (fun σ τ => Disjoint (analyticIntervalAtom I S σ) (analyticIntervalAtom I S τ)) := by
  intro σ τ hστ
  apply Set.disjoint_left.mpr
  intro x hx hy
  apply hστ
  funext z
  exact (hx.2 z).symm.trans (hy.2 z)

theorem analyticIntervalAtom_cover (I : Interval) (S : Finset ℝ) :
    (⋃ σ : S → Fin 3, analyticIntervalAtom I S σ) = I.carrier := by
  ext x
  simp only [Set.mem_iUnion]
  exact ⟨fun ⟨_, hx⟩ => hx.1,
    fun hx => ⟨fun z => oneDimensionalSign (x - z), hx, fun _ => rfl⟩⟩

/-- An atom containing one of its own cut points is a singleton. -/
theorem analyticIntervalAtom_subsingleton_of_cut (I : Interval) (S : Finset ℝ)
    (σ : S → Fin 3) {x : ℝ} (hx : x ∈ analyticIntervalAtom I S σ) (hcut : x ∈ S) :
    analyticIntervalAtom I S σ ⊆ {x} := by
  intro y hy
  have he := (hy.2 ⟨x, hcut⟩).trans (hx.2 ⟨x, hcut⟩).symm
  simp only [sub_self, oneDimensionalSign, lt_self_iff_false, ↓reduceIte] at he
  have : y - x = 0 := oneDimensionalSign_eq_one.mp he
  exact Set.mem_singleton_iff.mpr (sub_eq_zero.mp this)

/-- A finite family has one finite set containing every zero of each
member that is not identically zero on the interval. -/
theorem exists_analytic_interval_zero_cuts {ι : Type*} [Fintype ι]
    (I : Interval) (f : ι → ℝ → ℝ) (hf : ∀ i, AnalyticOnNhd ℝ (f i) I.carrier) :
    ∃ S : Finset ℝ, (↑S : Set ℝ) ⊆ I.carrier ∧
      ∀ i, (∃ t ∈ I.carrier, f i t ≠ 0) →
        ∀ x ∈ I.carrier, f i x = 0 → x ∈ S := by
  classical
  let Z (i : ι) : Set ℝ :=
    {x | x ∈ I.carrier ∧ f i x = 0 ∧ ∃ t ∈ I.carrier, f i t ≠ 0}
  have hZ (i : ι) : (Z i).Finite := by
    by_cases hn : ∃ t ∈ I.carrier, f i t ≠ 0
    · exact (analytic_zeros_finite_interval I (f i) (hf i) hn).subset
        (fun _ hx => ⟨hx.1, hx.2.1⟩)
    · have he : Z i = ∅ := by ext x; simp [Z, hn]
      rw [he]
      exact finite_empty
  have hU : (⋃ i, Z i).Finite := finite_iUnion hZ
  refine ⟨hU.toFinset, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hU.mem_toFinset.mp hx)
    exact hi.1
  · intro i hn x hx hz
    exact hU.mem_toFinset.mpr (mem_iUnion.mpr ⟨i, hx, hz, hn⟩)

/-- An analytic member has constant sign on each atom of a zero-cut set.
The proof also handles a member that vanishes identically. -/
theorem oneDimensionalSign_constant_on_atom (I : Interval) (S : Finset ℝ)
    (f : ℝ → ℝ) (hf : ContinuousOn f I.carrier)
    (hcuts : (∃ t ∈ I.carrier, f t ≠ 0) →
      ∀ x ∈ I.carrier, f x = 0 → x ∈ S) (σ : S → Fin 3) :
    ∃ c : Fin 3, ∀ x ∈ analyticIntervalAtom I S σ, oneDimensionalSign (f x) = c := by
  by_cases hn : ∃ t ∈ I.carrier, f t ≠ 0
  · by_cases hz : ∃ x ∈ analyticIntervalAtom I S σ, f x = 0
    · obtain ⟨x, hx, hfx⟩ := hz
      refine ⟨1, fun y hy => ?_⟩
      have hyx := analyticIntervalAtom_subsingleton_of_cut I S σ hx (hcuts hn x hx.1 hfx) hy
      rw [mem_singleton_iff] at hyx
      simpa only [hyx, hfx] using (oneDimensionalSign_eq_one.mpr (rfl : (0 : ℝ) = 0))
    · have hne : ∀ x ∈ analyticIntervalAtom I S σ, f x ≠ 0 := by
        intro x hx hfx
        exact hz ⟨x, hx, hfx⟩
      rcases (analyticIntervalAtom_isPreconnected I S σ).mapsTo_Ioi_or_Iio
        (hf.mono (analyticIntervalAtom_subset I S σ)) hne with hp | hm
      · exact ⟨2, fun x hx => oneDimensionalSign_eq_two.mpr (hp hx)⟩
      · exact ⟨0, fun x hx => oneDimensionalSign_eq_zero.mpr (hm hx)⟩
  · refine ⟨1, fun x hx => oneDimensionalSign_eq_one.mpr ?_⟩
    by_contra hfx
    exact hn ⟨x, hx.1, hfx⟩

/-- Actual finite, pairwise disjoint connected sign partition. Empty
atoms may be discarded; every nonempty atom is connected. The same cuts
work simultaneously for all sign conditions on the given finite family. -/
theorem exists_analytic_interval_sign_partition {ι : Type*} [Fintype ι]
    (I : Interval) (f : ι → ℝ → ℝ) (hf : ∀ i, AnalyticOnNhd ℝ (f i) I.carrier) :
    ∃ S : Finset ℝ, (↑S : Set ℝ) ⊆ I.carrier ∧
      Pairwise (fun σ τ => Disjoint (analyticIntervalAtom I S σ) (analyticIntervalAtom I S τ)) ∧
      (⋃ σ : S → Fin 3, analyticIntervalAtom I S σ) = I.carrier ∧
      (∀ σ : S → Fin 3, (analyticIntervalAtom I S σ).OrdConnected) ∧
      ∀ σ : S → Fin 3, ∃ v : ι → Fin 3,
        ∀ x ∈ analyticIntervalAtom I S σ, ∀ i, oneDimensionalSign (f i x) = v i := by
  classical
  obtain ⟨S, hS, hcuts⟩ := exists_analytic_interval_zero_cuts I f hf
  refine ⟨S, hS, analyticIntervalAtom_pairwiseDisjoint I S,
    analyticIntervalAtom_cover I S, analyticIntervalAtom_ordConnected I S, ?_⟩
  intro σ
  choose v hv using fun i => oneDimensionalSign_constant_on_atom I S (f i)
    (hf i).continuousOn (hcuts i) σ
  exact ⟨v, fun x hx i => hv i x hx⟩

end PlanarNikodym
