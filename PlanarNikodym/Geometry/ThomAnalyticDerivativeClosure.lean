import PlanarNikodym.Geometry.ThomMonicCylindricalClosure
import PlanarNikodym.Geometry.AnalyticPolynomialDerivativeNormalization
import PlanarNikodym.Geometry.ThomCylindricalLifting

/-! The exact closure step for the literal derivative extension of finitely
many prepared analytic monic polynomials, also inside an open vertical strip. -/
noncomputable section
open Set Polynomial
namespace PlanarNikodym

theorem closure_inter_isOpen_eq_on {X : Type*} [TopologicalSpace X]
    (S O : Set X) (hO : IsOpen O) :
    closure (S ∩ O) ∩ O = closure S ∩ O := by
  apply Set.Subset.antisymm
  · exact fun _ hx => ⟨closure_mono inter_subset_left hx.1, hx.2⟩
  · exact fun _ hx => ⟨mem_closure_inter_of_isOpen hx.1 hO hx.2, hx.2⟩

theorem analyticDerivativeThomCylinder_closure
    {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype J]
    (C V : Set E) (m : J → ℕ) (a : ∀ j, E → Fin (m j) → ℝ)
    (hV : IsOpen V) (hCV : C ⊆ V) (ha : ∀ j, AnalyticOnNhd ℝ (a j) V)
    (s : PolynomialDerivativeIndex m → Fin 3)
    (hne : ∀ x ∈ C, (polynomialThomFamilyCell false
      (polynomialDerivativeFamily (fun j => weierstrassPolynomial (a j x)) m) s).Nonempty) :
    let P := fun x => polynomialDerivativeFamily (fun j => weierstrassPolynomial (a j x)) m
    closure (polynomialThomCylinder C P s) ∩ (V ×ˢ univ) =
      {z | z.1 ∈ closure C ∩ V ∧ z.2 ∈ polynomialThomFamilyCell true (P z.1) s} := by
  dsimp only
  apply polynomialThomCylinder_closure_of_monic_normalization C V _ s
    (fun j => m j.1 - j.2.val)
    (fun j => weierstrassIteratedDerivativeCoefficients (a j.1) j.2.val)
    (fun j => ((m j.1).descFactorial j.2.val : ℝ)) hV hCV
  · intro j x hx
    exact (analyticAt_weierstrassIteratedDerivativeCoefficients
      (a j.1) j.2.val x (ha j.1 x hx)).continuousAt.continuousWithinAt
  · intro x _ j
    exact weierstrass_iterated_derivative_normalization (a j.1) j.2.val x
  · intro x _
    exact polynomialDerivativeFamily_stable _ m (fun j => by rw [weierstrassPolynomial_natDegree])
  · exact hne

/-- The same formula on an actual preparation cylinder. Restricting the
vertical coordinate to an open interval introduces no boundary assumption. -/
theorem analyticDerivativeCylindricalSignCell_closure
    {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype J]
    (C V : Set E) (m : J → ℕ) (a : ∀ j, E → Fin (m j) → ℝ)
    (hV : IsOpen V) (hCV : C ⊆ V) (ha : ∀ j, AnalyticOnNhd ℝ (a j) V)
    (A B : ℝ) (s : PolynomialDerivativeIndex m → Fin 3)
    (hne : ∀ x ∈ C, (polynomialThomFamilyCell false
      (polynomialDerivativeFamily (fun j => weierstrassPolynomial (a j x)) m) s).Nonempty) :
    let P := fun x => polynomialDerivativeFamily (fun j => weierstrassPolynomial (a j x)) m
    closure (polynomialCylindricalSignCell C A B P s) ∩ (V ×ˢ Ioo A B) =
      {z | z.1 ∈ closure C ∩ V ∧ z.2 ∈ Ioo A B ∧
        z.2 ∈ polynomialThomFamilyCell true (P z.1) s} := by
  dsimp only
  let P := fun x => polynomialDerivativeFamily (fun j => weierstrassPolynomial (a j x)) m
  have hcl := analyticDerivativeThomCylinder_closure C V m a hV hCV ha s hne
  have he : polynomialCylindricalSignCell C A B P s =
      polynomialThomCylinder C P s ∩ (univ ×ˢ Ioo A B) := by
    ext z
    exact ⟨fun hz => ⟨⟨hz.1.1, hz.2⟩, mem_univ _, hz.1.2⟩,
      fun hz => ⟨⟨hz.1.1, hz.2.2⟩, hz.1.2⟩⟩
  change closure (polynomialCylindricalSignCell C A B P s) ∩ (V ×ˢ Ioo A B) = _
  rw [he]
  have hlocal := closure_inter_isOpen_eq_on (polynomialThomCylinder C P s)
    (univ ×ˢ Ioo A B) (isOpen_univ.prod isOpen_Ioo)
  ext z
  constructor
  · rintro ⟨hz, hzV, hzt⟩
    have hz' : z ∈ closure (polynomialThomCylinder C P s) :=
      closure_mono inter_subset_left hz
    have hw := (Set.ext_iff.mp hcl z).mp ⟨hz', hzV, mem_univ _⟩
    exact ⟨hw.1, hzt, hw.2⟩
  · rintro ⟨hx, ht, hw⟩
    have hz' := (Set.ext_iff.mp hcl z).mpr ⟨hx, hw⟩
    exact ⟨((Set.ext_iff.mp hlocal z).mpr ⟨hz'.1, mem_univ _, ht⟩).1, hx.2, ht⟩

end PlanarNikodym
