import PlanarNikodym.Tame.RestrictedAnalyticLanguage

noncomputable section
open Set Metric

namespace PlanarNikodym

/-- The graph over a specified domain; this does not assert that an
arbitrary ambient extension of the function is globally definable. -/
def RanDefinableOn {ι : Type*} (f : (ι → ℝ) → ℝ) (S : Set (ι → ℝ)) : Prop :=
  RanDefinable {x : Option ι → ℝ | x ∘ some ∈ S ∧ f (x ∘ some) = x none}

theorem RanDefinableFun.ranDefinableOn {ι : Type*} {f : (ι → ℝ) → ℝ}
    (hf : RanDefinableFun f) {S : Set (ι → ℝ)} (hS : RanDefinable S) :
    RanDefinableOn f S :=
  (hS.preimage_comp some).inter hf

theorem RanDefinableOn.congr {ι : Type*} {f g : (ι → ℝ) → ℝ}
    {S : Set (ι → ℝ)} (hf : RanDefinableOn f S) (hfg : EqOn f g S) :
    RanDefinableOn g S := by
  unfold RanDefinableOn at hf ⊢
  convert hf using 1
  ext x
  exact and_congr_right fun hx => by rw [hfg hx]

theorem RanDefinableOn.restrict {ι : Type*} {f : (ι → ℝ) → ℝ}
    {S T : Set (ι → ℝ)} (hf : RanDefinableOn f S) (hT : RanDefinable T)
    (hTS : T ⊆ S) : RanDefinableOn f T := by
  unfold RanDefinableOn at hf ⊢
  convert hf.inter (hT.preimage_comp some) using 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
  exact ⟨fun h => ⟨⟨hTS h.1, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩

theorem RanDefinableOn.finite_union {ι κ : Type*} [Finite κ]
    {f : (ι → ℝ) → ℝ} {S : κ → Set (ι → ℝ)}
    (h : ∀ i, RanDefinableOn f (S i)) : RanDefinableOn f (⋃ i, S i) := by
  unfold RanDefinableOn at h ⊢
  convert Set.definable_iUnion_of_finite h using 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  exact ⟨fun ⟨⟨i, hi⟩, hx⟩ => ⟨i, hi, hx⟩,
    fun ⟨i, hi, hx⟩ => ⟨⟨i, hi⟩, hx⟩⟩

theorem RanDefinableOn.preimage_map {ι κ : Type*} [Finite ι] [Finite κ]
    {f : (ι → ℝ) → ℝ} {S : Set (ι → ℝ)} (hf : RanDefinableOn f S)
    {F : (κ → ℝ) → (ι → ℝ)} (hF : RanDefinableMap F) :
    RanDefinableOn (f ∘ F) (F ⁻¹' S) := by
  let H : (Option κ → ℝ) → (Option ι → ℝ) := fun x =>
    fun i => Option.elim i (x none) (F (x ∘ some))
  have hH : RanDefinableMap H := by
    intro i
    cases i with
    | none => exact ranDefinableFun_coordinate none
    | some i => exact (hF i).comp (fun j => ranDefinableFun_coordinate (some j))
  exact Set.Definable.preimage_map hH hf

theorem RanDefinableOn.sublevel {ι : Type*} [Finite ι] {f : (ι → ℝ) → ℝ}
    {S : Set (ι → ℝ)} (hf : RanDefinableOn f S) (c : ℝ) :
    RanDefinable {x | x ∈ S ∧ f x < c} := by
  have hlt : RanDefinable {x : Option ι → ℝ | x none < c} :=
    ranDefinable_lt (ranDefinableFun_coordinate none) (ranDefinableFun_const c)
  have h := (hf.inter hlt).image_comp some
  convert h using 1
  ext x
  constructor
  · rintro ⟨hx, hc⟩
    exact ⟨(fun i => Option.elim i (f x) x), ⟨⟨hx, rfl⟩, hc⟩, rfl⟩
  · rintro ⟨y, ⟨⟨hy, he⟩, hc⟩, rfl⟩
    exact ⟨hy, he ▸ hc⟩

theorem ranDefinable_Icc {ι : Type*} [Finite ι] (a b : ι → ℝ) :
    RanDefinable (Icc a b) := by
  have h (i : ι) : RanDefinable {x : ι → ℝ | a i ≤ x i ∧ x i ≤ b i} :=
    (ranDefinable_le (ranDefinableFun_const (a i)) (ranDefinableFun_coordinate i)).inter
      (ranDefinable_le (ranDefinableFun_coordinate i) (ranDefinableFun_const (b i)))
  convert Set.definable_iInter_of_finite h using 1
  ext x
  simp only [Set.mem_Icc, Pi.le_def, Set.mem_iInter, Set.mem_setOf_eq]
  exact forall_and.symm

theorem ranDefinable_ball {ι : Type*} [Fintype ι] (c : ι → ℝ) (r : ℝ) :
    RanDefinable (ball c r) := by
  by_cases hr : 0 < r
  · have h (i : ι) : RanDefinable {x : ι → ℝ | c i - r < x i ∧ x i < c i + r} :=
      (ranDefinable_lt (ranDefinableFun_const (c i - r))
        (ranDefinableFun_coordinate i)).inter
      (ranDefinable_lt (ranDefinableFun_coordinate i)
        (ranDefinableFun_const (c i + r)))
    convert Set.definable_iInter_of_finite h using 1
    ext x
    simp only [mem_ball, dist_pi_lt_iff hr, Real.dist_eq, abs_lt,
      Set.mem_iInter, Set.mem_setOf_eq]
    exact forall_congr' fun i => by constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  · rw [ball_eq_empty.mpr (le_of_not_gt hr)]
    exact Set.definable_empty

theorem ranDefinableOn_restrictedAnalytic {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : AnalyticOnNhd ℝ f (restrictedAnalyticCube n)) :
    RanDefinableOn f (restrictedAnalyticCube n) := by
  apply (ranDefinableFun_restrictedAnalytic f hf).ranDefinableOn
    (ranDefinable_Icc (-1) 1) |>.congr
  intro x hx
  change x ∈ restrictedAnalyticCube n at hx
  simp [restrictedAnalyticFunction, hx]

end PlanarNikodym
