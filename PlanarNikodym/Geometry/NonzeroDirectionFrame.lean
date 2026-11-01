import PlanarNikodym.Geometry.LocalCoordinates

/-! Actual linear coordinates whose last coordinate is any prescribed nonzero
real vector. Invertibility is proved, not assumed as a frame certificate. -/
noncomputable section
open Set
namespace PlanarNikodym

def realCoordinateSplitEquiv {d : ℕ} (j : Fin (d + 1)) :
    ((Fin d → ℝ) × ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ) :=
  ({ toFun := fun p => j.insertNth p.2 p.1
     invFun := fun p => (j.removeNth p, p j)
     left_inv := by intro p; simp only [Fin.removeNth_insertNth, Fin.insertNth_apply_same]
     right_inv := by intro p; exact Fin.insertNth_self_removeNth j p
     map_add' := by
       intro p q
       funext i
       by_cases hi : i = j
       · subst i; simp
       · by_cases hij : i < j <;> simp [Fin.insertNth, Fin.succAboveCases, hi, hij]
     map_smul' := by
       intro c p
       funext i
       by_cases hi : i = j <;> simp [Fin.insertNth, Fin.succAboveCases, hi] } :
    ((Fin d → ℝ) × ℝ) ≃ₗ[ℝ] (Fin (d + 1) → ℝ)).toContinuousLinearEquiv

theorem realCoordinateSplitEquiv_vertical {d : ℕ} (j : Fin (d + 1)) :
    realCoordinateSplitEquiv j (0, 1) = Pi.single j 1 := by
  funext i
  by_cases hi : i = j <;> simp [realCoordinateSplitEquiv, hi]

/-- A rank-one modification of the identity taking the j-th coordinate
vector to v, invertible precisely when the j-th component of v is nonzero. -/
theorem exists_real_direction_linear_equiv {d : ℕ} (v : Fin (d + 1) → ℝ)
    (j : Fin (d + 1)) (hv : v j ≠ 0) :
    ∃ e : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ), e (Pi.single j 1) = v := by
  classical
  let L : (Fin (d + 1) → ℝ) →L[ℝ] (Fin (d + 1) → ℝ) :=
    ContinuousLinearMap.id ℝ _ + (ContinuousLinearMap.proj j).smulRight (v - Pi.single j 1)
  have hL (x : Fin (d + 1) → ℝ) : L x = x + x j • (v - Pi.single j 1) := rfl
  have hi : Function.Injective L := by
    intro x y h
    have hj := congrFun h j
    simp only [hL, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same, smul_eq_mul] at hj
    have he : x j * v j = y j * v j := by nlinarith
    have hxy : x j = y j := mul_right_cancel₀ hv he
    rw [hL, hL, hxy] at h
    exact add_right_cancel h
  let e := (LinearEquiv.ofBijective L.toLinearMap
    ⟨hi, LinearMap.surjective_of_injective hi⟩).toContinuousLinearEquiv
  refine ⟨e, ?_⟩
  change L (Pi.single j 1) = v
  rw [hL]
  simp

/-- The prescribed direction is the actual image of the last coordinate. -/
theorem exists_real_nonzero_direction_frame {d : ℕ} (v : Fin (d + 1) → ℝ) (hv : v ≠ 0) :
    ∃ e : ((Fin d → ℝ) × ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ),
      ∀ t : ℝ, e (0, t) = t • v := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨L, hL⟩ := exists_real_direction_linear_equiv v j hj
  let e := (realCoordinateSplitEquiv j).trans L
  have he : e (0, 1) = v := by
    change L (realCoordinateSplitEquiv j (0, 1)) = v
    rw [realCoordinateSplitEquiv_vertical, hL]
  refine ⟨e, ?_⟩
  intro t
  have ht : ((0, t) : (Fin d → ℝ) × ℝ) = t • (0, 1) := by simp
  rw [ht, map_smul, he]

end PlanarNikodym
