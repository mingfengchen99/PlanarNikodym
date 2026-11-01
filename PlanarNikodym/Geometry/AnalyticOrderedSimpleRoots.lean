import PlanarNikodym.Geometry.AnalyticSimpleRootBranches

/-! The complete strictly ordered analytic root atlas of a compact simple-root fiber.
The common parameter neighborhood is an actual positive-radius ball. -/

noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- All simple roots on a compact interval continue as one finite strictly ordered
analytic family on a common ball, and these branches exhaust every nearby zero.
In particular no unproved root-covering or no-new-roots condition is assumed. -/
theorem exists_ordered_analytic_simple_root_branches
    (f : E × ℝ → ℝ) (x₀ : E) (A B : ℝ) (_hAB : A < B)
    (hf : ∀ t ∈ Icc A B, AnalyticAt ℝ f (x₀, t))
    (hA : f (x₀, A) ≠ 0) (hB : f (x₀, B) ≠ 0)
    (hd : ∀ t ∈ Ioo A B, f (x₀, t) = 0 →
      deriv (fun s => f (x₀, s)) t ≠ 0) :
    ∃ (n : ℕ) (ε : ℝ), 0 < ε ∧ ∃ ρ : Fin n → E → ℝ,
      (∀ i, AnalyticOnNhd ℝ (ρ i) (Metric.ball x₀ ε)) ∧
      (∀ x ∈ Metric.ball x₀ ε, StrictMono (fun i => ρ i x)) ∧
      (∀ x ∈ Metric.ball x₀ ε, ∀ i, ρ i x ∈ Ioo A B) ∧
      ∀ x ∈ Metric.ball x₀ ε, ∀ t ∈ Ioo A B,
        f (x, t) = 0 ↔ ∃ i, t = ρ i x := by
  classical
  have hinter (t : ℝ) (ht : t ∈ Icc A B) (hz : f (x₀, t) = 0) :
      t ∈ Ioo A B := by
    have hta : t ≠ A := by intro h; subst t; exact hA hz
    have htb : t ≠ B := by intro h; subst t; exact hB hz
    exact ⟨lt_of_le_of_ne ht.1 hta.symm, lt_of_le_of_ne ht.2 htb⟩
  have hfin : {t : ℝ | t ∈ Icc A B ∧ f (x₀, t) = 0}.Finite :=
    finite_simple_analytic_fiber_zeros f x₀ A B hf
      (fun t ht hz => hd t (hinter t ht hz) hz)
  let S : Finset ℝ := hfin.toFinset
  let t : Fin S.card ↪o ℝ := S.orderEmbOfFin rfl
  have ht (i : Fin S.card) : t i ∈ Icc A B ∧ f (x₀, t i) = 0 := by
    exact hfin.mem_toFinset.mp (S.orderEmbOfFin_mem rfl i)
  have htI (i : Fin S.card) : t i ∈ Ioo A B :=
    hinter (t i) (ht i).1 (ht i).2
  have hrootRange (s : ℝ) (hs : s ∈ Icc A B) (hz : f (x₀, s) = 0) :
      ∃ i, t i = s := by
    have hsS : s ∈ S := hfin.mem_toFinset.mpr ⟨hs, hz⟩
    apply Set.mem_range.mp
    change s ∈ Set.range (S.orderEmbOfFin rfl)
    rw [Finset.range_orderEmbOfFin]
    exact hsS
  have hb (i : Fin S.card) :
      ∃ (U : Set E) (V : Set ℝ) (ρ : E → ℝ),
        IsOpen U ∧ x₀ ∈ U ∧ IsOpen V ∧ t i ∈ V ∧ ρ x₀ = t i ∧
        MapsTo ρ U V ∧ AnalyticOnNhd ℝ ρ U ∧
        ∀ x ∈ U, ∀ s ∈ V, f (x, s) = 0 ↔ s = ρ x :=
    exists_analytic_simple_root_branch f x₀ (t i) (hf _ (ht i).1) (ht i).2
      (hd _ (htI i) (ht i).2)
  choose U V ρ hU hxU hV htV hρ₀ hρV hρ hroot using hb
  let K : Set ℝ := Icc A B \ ⋃ i, V i
  have hK : IsCompact K := isCompact_Icc.diff (isOpen_iUnion hV)
  have hKn : ∀ s ∈ K, f (x₀, s) ≠ 0 := by
    intro s hs hz
    obtain ⟨i, hi⟩ := hrootRange s hs.1 hz
    exact hs.2 (mem_iUnion.mpr ⟨i, hi ▸ htV i⟩)
  obtain ⟨W, hW, hxW, hWn⟩ := exists_open_nhds_compact_fiber_nonzero f x₀ K hK
    (fun s hs => (hf s hs.1).continuousAt) hKn
  have hnearU : ∀ᶠ x in 𝓝 x₀, ∀ i, x ∈ U i :=
    eventually_all.mpr (fun i => (hU i).mem_nhds (hxU i))
  have hnearI : ∀ᶠ x in 𝓝 x₀, ∀ i, ρ i x ∈ Ioo A B := by
    apply eventually_all.mpr
    intro i
    apply (hρ i x₀ (hxU i)).continuousAt.eventually
    exact isOpen_Ioo.mem_nhds (by simpa only [hρ₀ i] using htI i)
  have hnearOrder : ∀ᶠ x in 𝓝 x₀, StrictMono (fun i => ρ i x) := by
    have hp : ∀ i j : Fin S.card,
        ∀ᶠ x in 𝓝 x₀, i < j → ρ i x < ρ j x := by
      intro i j
      by_cases hij : i < j
      · have hlt : ρ i x₀ < ρ j x₀ := by
          simpa only [hρ₀ i, hρ₀ j] using t.strictMono hij
        exact ((hρ i x₀ (hxU i)).continuousAt.eventually_lt
          (hρ j x₀ (hxU j)).continuousAt hlt).mono (fun _ h _ => h)
      · exact Eventually.of_forall (fun _ h => (hij h).elim)
    exact (eventually_all.mpr fun i => eventually_all.mpr (hp i)).mono
      (fun _ h i j hij => h i j hij)
  have hall : {x | x ∈ W ∧ (∀ i, x ∈ U i) ∧
      (∀ i, ρ i x ∈ Ioo A B) ∧ StrictMono (fun i => ρ i x)} ∈ 𝓝 x₀ := by
    filter_upwards [hW.mem_nhds hxW, hnearU, hnearI, hnearOrder] with x hxW hxU hxI hxO
    exact ⟨hxW, hxU, hxI, hxO⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨S.card, ε, hε, ρ, ?_, ?_, ?_, ?_⟩
  · intro i x hx
    exact hρ i x ((hball hx).2.1 i)
  · intro x hx
    exact (hball hx).2.2.2
  · intro x hx i
    exact (hball hx).2.2.1 i
  · intro x hx s hs
    constructor
    · intro hz
      have hsV : s ∈ ⋃ i, V i := by
        by_contra hn
        exact hWn x (hball hx).1 s ⟨⟨hs.1.le, hs.2.le⟩, hn⟩ hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hsV
      exact ⟨i, (hroot i x ((hball hx).2.1 i) s hi).mp hz⟩
    · rintro ⟨i, rfl⟩
      exact (hroot i x ((hball hx).2.1 i) (ρ i x)
        (hρV i ((hball hx).2.1 i))).mpr rfl

end PlanarNikodym
