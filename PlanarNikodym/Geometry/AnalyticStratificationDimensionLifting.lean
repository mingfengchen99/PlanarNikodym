import PlanarNikodym.Geometry.AnalyticStratificationFrontier

/-! The complete graph/band comparison reducing strict frontier dimension
drop to that of the base. The extra root equation is an actual monic
polynomial equation, not an assumed dimension or manifold certificate. -/
noncomputable section
open Set Polynomial
namespace PlanarNikodym

theorem cylindrical_frontier_dimension_lifting
    {E I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (Q : I → AnalyticStratificationChart E) (hQU : ∀ i, (Q i).image ⊆ U)
    (n : I → ℕ) (c : (i : I) → Fin (n i + 2) → E → ℝ)
    (ha : ∀ i k, AnalyticOnNhd ℝ (c i k) (Q i).image)
    (hc : ∀ i x, x ∈ (Q i).image → StrictMono (fun k => c i k x))
    (hbase : ∀ i j, i ≠ j → ((Q j).image ∩ closure (Q i).image).Nonempty →
      (Q j).dim < (Q i).dim)
    (hgraph : ∀ i (l : Fin (n i)), ∃ (m : ℕ) (a : E → Fin m → ℝ),
      (∀ x ∈ U, ContinuousAt a x) ∧
      ∀ z ∈ analyticGraph (Q i).image (c i l.castSucc.succ),
        (weierstrassPolynomial (a z.1)).eval z.2 = 0) :
    let P := fun p : (i : I) × (Fin (n i) ⊕ Fin (n i + 1)) =>
      (Q p.1).cylindrical (c p.1) (ha p.1) (hc p.1) p.2
    (∀ p q, ((P q).image ∩ closure (P p).image).Nonempty →
      (P q).image ⊆ closure (P p).image) →
    ∀ p q, p ≠ q → ((P q).image ∩ closure (P p).image).Nonempty →
      (P q).dim < (P p).dim := by
  dsimp only
  intro hfront p q hpq hne
  obtain ⟨i, a⟩ := p
  obtain ⟨j, b⟩ := q
  by_cases hij : i = j
  · subst j
    have hab : a ≠ b := fun he => hpq (congrArg (Sigma.mk i) he)
    exact cylindrical_same_base_frontier_dimension (Q i) (c i) (ha i) (hc i) a b hab hne
  · obtain ⟨z, hzq, hzp⟩ := hne
    have hxj : z.1 ∈ (Q j).image := by
      rw [AnalyticStratificationChart.cylindrical_image] at hzq
      exact mem_analyticCylindricalCell_fst hzq
    have hxi : z.1 ∈ closure (Q i).image :=
      continuous_fst.continuousAt.continuousWithinAt.mem_closure hzp (by
        intro w hw
        rw [AnalyticStratificationChart.cylindrical_image] at hw
        exact mem_analyticCylindricalCell_fst hw)
    have hdim := hbase i j hij ⟨z.1, hxj, hxi⟩
    rcases a with a | a
    · rcases b with b | b
      · simpa only [AnalyticStratificationChart.cylindrical,
          AnalyticStratificationChart.graph_dim] using hdim
      · have hsub := hfront ⟨i, Sum.inl a⟩ ⟨j, Sum.inr b⟩ ⟨z, hzq, hzp⟩
        obtain ⟨m, A, hA, hzero⟩ := hgraph i a
        obtain ⟨x, hx⟩ := (Q j).connected_image.nonempty
        have hlt : c j b.castSucc x < c j b.succ x :=
          hc j x hx (by change (b : ℕ) < (b : ℕ) + 1; omega)
        apply False.elim
        apply monic_zero_set_closure_not_contains_vertical_interval A
          (analyticGraph (Q i).image (c i a.castSucc.succ)) hzero x (hA x (hQU j hx))
          (c j b.castSucc x) (c j b.succ x) hlt
        intro w hw
        have hwx : w.1 = x := mem_singleton_iff.mp hw.1
        have hwBand : w ∈ ((Q j).cylindrical (c j) (ha j) (hc j) (Sum.inr b)).image := by
          rw [AnalyticStratificationChart.cylindrical_image]
          change w.1 ∈ (Q j).image ∧ c j b.castSucc w.1 < w.2 ∧ w.2 < c j b.succ w.1
          exact ⟨hwx ▸ hx, hwx ▸ hw.2⟩
        have hwCl := hsub hwBand
        simpa only [AnalyticStratificationChart.cylindrical_image, analyticCylindricalCell] using hwCl
    · have hle := (Q j).cylindrical_dim_le (c j) (ha j) (hc j) b
      change ((Q j).cylindrical (c j) (ha j) (hc j) b).dim < (Q i).dim + 1
      omega

end PlanarNikodym
