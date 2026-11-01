import PlanarNikodym.Geometry.AnalyticRegularStratumPartition
import PlanarNikodym.Geometry.AnalyticSignCellBarrier

/-! Actual finite barrier patches for bounded semianalytic sets. The
barriers, regular equations and compact boxes are all constructed from
the local sign description; none is an input to the covering theorem. -/
noncomputable section
open Set Metric
namespace PlanarNikodym

structure SemianalyticBarrierPatch (n : ℕ) where
  chart : AnalyticStratificationChart (Fin n → ℝ)
  semianalytic : LocallySemianalytic chart.image
  window : Set (Fin n → ℝ)
  image_window : chart.image ⊆ window
  regular : RegularStratumEquations (closure window) chart.image chart.dim
  center : Fin n → ℝ
  radius : ℝ
  radius_pos : 0 < radius
  box_window : closedBall center radius ⊆ window
  barrier : (Fin n → ℝ) → ℝ
  analytic_barrier : AnalyticOnNhd ℝ barrier (closure window)
  positive_barrier : ∀ x ∈ chart.image ∩ ball center radius, 0 < barrier x
  zero_boundary : ∀ x ∈ closure (chart.image ∩ ball center radius) \
    (chart.image ∩ ball center radius), barrier x = 0

def SemianalyticBarrierPatch.piece {n : ℕ} (P : SemianalyticBarrierPatch n) :
    Set (Fin n → ℝ) := P.chart.image ∩ ball P.center P.radius

theorem SemianalyticAt.exists_local_barrier_cover
    {n : ℕ} {A : Set (Fin n → ℝ)} {x : Fin n → ℝ} (hA : SemianalyticAt A x) :
    ∃ r : ℝ, 0 < r ∧
      ∃ (ι : Type) (_ : Fintype ι) (P : ι → SemianalyticBarrierPatch n),
        (∀ i, (P i).chart.image ⊆ A) ∧ (⋃ i, (P i).piece) = A ∩ ball x r := by
  classical
  obtain ⟨O, hO, hxO, J, hJ, f, hf, R, hrep⟩ := hA
  obtain ⟨U, hU, hxU, hUO, hUsemi, κ, hκ, g, η, hg, hinc, href, hregular⟩ :=
    localAnalyticRegularRefinement_fin n f x (fun j => hf j x hxO) O hO hxO
  obtain ⟨r, hr, hbox⟩ := Metric.isOpen_iff.mp hU x hxU
  let t := r / 2
  have ht : 0 < t := by dsimp [t]; linarith
  have hclosed : closedBall x t ⊆ U := fun y hy => hbox (by
    rw [mem_ball]
    exact (mem_closedBall.mp hy).trans_lt (by dsimp [t]; linarith))
  let I := {s : κ → Fin 3 // (analyticStrongSignCell U g s).Nonempty}
  have hex (s : I) : ∃ Q : AnalyticStratificationChart (Fin n → ℝ),
      Q.image = analyticStrongSignCell U g s ∧ Q.dim = η s := by
    rcases href.1 s with he | ⟨Q, hQ, hdim, _⟩
    · exact (s.property.ne_empty he).elim
    · exact ⟨Q, hQ, hdim⟩
  choose Q hQ hdim using hex
  have hQU (s : I) : (Q s).image ⊆ U := by rw [hQ s]; exact fun _ hz => hz.1
  have hconstant (s : I) {y z : Fin n → ℝ} (hy : y ∈ (Q s).image)
      (hz : z ∈ (Q s).image) : y ∈ A ↔ z ∈ A := by
    rw [hrep y (hUO (subset_closure (hQU s hy))),
      hrep z (hUO (subset_closure (hQU s hz)))]
    have he : (fun j => oneDimensionalSign (f j y)) =
        fun j => oneDimensionalSign (f j z) := by
      funext j
      obtain ⟨k, hk⟩ := hinc j
      rw [← hk (hQU s hy), ← hk (hQU s hz)]
      rw [hQ s] at hy hz
      exact (hy.2 k).trans (hz.2 k).symm
    rw [he]
  have hbar (s : I) := exists_analytic_sign_piece_barrier U hU g hg s x t ht hclosed
  choose b hb hp hz using hbar
  let T := {s : I // (Q s).image ⊆ A}
  let P (i : T) : SemianalyticBarrierPatch n :=
    { chart := Q i.val
      semianalytic := by rw [hQ i.val]; exact
        analyticStrongSignCell_locallySemianalytic_of_closed_window hUsemi g hg i.val
      window := U
      image_window := hQU i.val
      regular := by rw [hQ i.val, hdim i.val]; exact hregular _ i.val.property
      center := x
      radius := t
      radius_pos := ht
      box_window := hclosed
      barrier := b i.val
      analytic_barrier := hb i.val
      positive_barrier := by simpa only [← hQ i.val] using hp i.val
      zero_boundary := by simpa only [← hQ i.val] using hz i.val }
  refine ⟨t, ht, T, inferInstance, P, fun i => i.property, ?_⟩
  ext y
  constructor
  · intro hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    exact ⟨i.property hi.1, hi.2⟩
  · rintro ⟨hyA, hyb⟩
    have hyU := hclosed (ball_subset_closedBall hyb)
    let s : κ → Fin 3 := fun k => oneDimensionalSign (g k y)
    have hys : y ∈ analyticStrongSignCell U g s := ⟨hyU, fun _ => rfl⟩
    let a : I := ⟨s, y, hys⟩
    have hyQ : y ∈ (Q a).image := (hQ a).symm ▸ hys
    have haA : (Q a).image ⊆ A := fun z hz => (hconstant a hyQ hz).mp hyA
    exact mem_iUnion.mpr ⟨⟨a, haA⟩, hyQ, hyb⟩

theorem LocallySemianalytic.exists_finite_barrier_cover
    {n : ℕ} {A : Set (Fin n → ℝ)} (hA : LocallySemianalytic A)
    (hb : Bornology.IsBounded A) :
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → SemianalyticBarrierPatch n),
      (∀ i, (P i).chart.image ⊆ A) ∧ (⋃ i, (P i).piece) = A := by
  classical
  have hl (x : _root_.closure A) := SemianalyticAt.exists_local_barrier_cover (hA x.val)
  choose r hr I hI P hsub hcover using hl
  letI (x : _root_.closure A) : Fintype (I x) := hI x
  obtain ⟨s, hs⟩ := hb.isCompact_closure.elim_finite_subcover
    (fun x : _root_.closure A => ball x.val (r x)) (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr _)⟩)
  refine ⟨(x : s) × I x.val, inferInstance, (fun i => P i.1.val i.2),
    (fun i => hsub i.1.val i.2), ?_⟩
  ext y
  constructor
  · intro hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    exact hsub i.1.val i.2 hi.1
  · intro hy
    obtain ⟨x, hxs, hyb⟩ := mem_iUnion₂.mp (hs (subset_closure hy))
    have hyp : y ∈ ⋃ i, (P x i).piece := (hcover x).symm ▸ (show y ∈ A ∩ ball x.val (r x) from ⟨hy, hyb⟩)
    obtain ⟨i, hi⟩ := mem_iUnion.mp hyp
    exact mem_iUnion.mpr ⟨⟨⟨x, hxs⟩, i⟩, hi⟩

end PlanarNikodym
