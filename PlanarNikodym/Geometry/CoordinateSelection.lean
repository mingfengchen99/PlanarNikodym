import PlanarNikodym.Geometry.LocalCoordinates
import PlanarNikodym.Core.Definitions

noncomputable section
open Set Submodule Module Function
namespace PlanarNikodym

/-- Select effective coordinate directions and extend them to a permutation
of the original coordinates. This is a finite-dimensional algebraic step. -/
theorem exists_effective_split {V : Type*} [AddCommGroup V] [Module ℝ V]
    {d m : ℕ} (L : Aux d →ₗ[ℝ] V) (hr : finrank ℝ L.range = m) :
    ∃ e : (Aux m × Aux (d - m)) ≃L[ℝ] Aux d,
      Function.Injective (fun w : Aux m => L (e (w, 0))) := by
  classical
  let f : Fin d → V := fun i => L (Pi.single i 1)
  let hs₀ := linearIndepOn_empty ℝ f
  let s : Set (Fin d) := hs₀.extend (empty_subset univ)
  have hs : LinearIndepOn ℝ f s := hs₀.linearIndepOn_extend (empty_subset univ)
  have hspan : span ℝ (range (fun i : s => f i)) = L.range := by
    rw [← Set.image_eq_range f s]
    have h := hs₀.span_image_extend_eq_span_image (empty_subset univ)
    simpa only [Set.image_univ, ← range_eq_span_coordinates, f] using h
  have hcard : Fintype.card s = m := by
    have h := finrank_span_eq_card hs
    rw [hspan, hr] at h
    exact h.symm
  let es : Fin m ≃ s := Fintype.equivOfCardEq (by simp [hcard])
  let ec : Fin (d - m) ≃ (sᶜ : Set (Fin d)) :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, Fintype.card_compl_set, Fintype.card_fin, hcard])
  let ei : Fin m ⊕ Fin (d - m) ≃ Fin d := (Equiv.sumCongr es ec).trans (Equiv.Set.sumCompl s)
  let e : (Aux m × Aux (d - m)) ≃L[ℝ] Aux d :=
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin m) (Fin (d - m)) (fun _ => ℝ)).symm.trans
      (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin d => ℝ) ei)
  have he (j : Fin m) : e (Pi.single j 1, 0) = Pi.single (ei (Sum.inl j)) 1 := by
    ext i
    obtain ⟨i, rfl⟩ := ei.surjective i
    change (Equiv.piCongrLeft (fun _ : Fin d => ℝ) ei
      ((Equiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin (d - m) => ℝ)).symm
        (Pi.single j 1, 0))) (ei i) = _
    rw [Equiv.piCongrLeft_apply_apply]
    cases i with
    | inl k => simp [Equiv.sumPiEquivProdPi, Pi.single_apply, ei.injective.eq_iff]
    | inr k => simp [Equiv.sumPiEquivProdPi, ei.injective.eq_iff]
  have hli : LinearIndependent ℝ (fun j : Fin m => L (e (Pi.single j 1, 0))) := by
    simp_rw [he]
    exact hs.comp (fun j => es j) es.injective
  let A : Aux m →ₗ[ℝ] V :=
    L.comp (e.toLinearMap.comp (LinearMap.inl ℝ (Aux m) (Aux (d - m))))
  have hc : finrank ℝ A.range = m := by
    rw [range_eq_span_coordinates]
    change finrank ℝ (span ℝ (range (fun j : Fin m => L (e (Pi.single j 1, 0))))) = m
    exact (finrank_span_eq_card hli).trans (Fintype.card_fin m)
  have hker := A.finrank_range_add_finrank_ker
  rw [hc] at hker
  have hk : finrank ℝ A.ker = 0 := by simpa using hker
  have hi : Function.Injective A := LinearMap.ker_eq_bot.mp ((finrank_eq_zero).mp hk)
  exact ⟨e, hi⟩

end PlanarNikodym
