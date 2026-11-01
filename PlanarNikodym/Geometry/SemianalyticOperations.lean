import PlanarNikodym.Geometry.SemianalyticAnalyticSignDomains

/-! Actual Boolean and analytic inverse-image operations for the local
analytic-sign definition of semianalyticity. No projection closure is assumed. -/
noncomputable section
open Set
namespace PlanarNikodym

theorem LocallySemianalytic.compl {n : ℕ} {A : Set (Fin n → ℝ)}
    (hA : LocallySemianalytic A) : LocallySemianalytic Aᶜ := by
  intro x
  obtain ⟨O, hO, hx, J, hJ, f, hf, Q, he⟩ := hA x
  exact ⟨O, hO, hx, J, hJ, f, hf, (fun s => ¬ Q s), fun y hy => (he y hy).not⟩

theorem LocallySemianalytic.inter {n : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : LocallySemianalytic A) (hB : LocallySemianalytic B) : LocallySemianalytic (A ∩ B) := by
  intro x
  obtain ⟨O, hO, hxO, J, hJ, f, hf, Q, he⟩ := hA x
  obtain ⟨V, hV, hxV, K, hK, g, hg, R, hr⟩ := hB x
  refine ⟨O ∩ V, hO.inter hV, ⟨hxO, hxV⟩, J ⊕ K, inferInstance, Sum.elim f g, ?_,
    (fun s => Q (fun j => s (Sum.inl j)) ∧ R (fun k => s (Sum.inr k))), ?_⟩
  · rintro (j | k) y hy
    · exact hf j y hy.1
    · exact hg k y hy.2
  · intro y hy
    exact (he y hy.1).and (hr y hy.2)

theorem LocallySemianalytic.union {n : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : LocallySemianalytic A) (hB : LocallySemianalytic B) : LocallySemianalytic (A ∪ B) := by
  simpa only [compl_inter, compl_compl] using (hA.compl.inter hB.compl).compl

theorem LocallySemianalytic.iInter {n : ℕ} {ι : Type} [Fintype ι]
    (A : ι → Set (Fin n → ℝ)) (hA : ∀ i, LocallySemianalytic (A i)) :
    LocallySemianalytic (⋂ i, A i) := by
  classical
  intro x
  choose O hO hxO J hJ f hf Q he using fun i => hA i x
  letI (i : ι) : Fintype (J i) := hJ i
  refine ⟨⋂ i, O i, isOpen_iInter_of_finite hO, mem_iInter.mpr hxO,
    Σ i, J i, inferInstance, (fun j => f j.1 j.2), ?_,
    (fun s => ∀ i, Q i (fun j => s ⟨i, j⟩)), ?_⟩
  · intro j y hy
    exact hf j.1 j.2 y (mem_iInter.mp hy j.1)
  · intro y hy
    simp only [mem_iInter]
    exact forall_congr' (fun i => he i y (mem_iInter.mp hy i))

theorem LocallySemianalytic.iUnion {n : ℕ} {ι : Type} [Fintype ι]
    (A : ι → Set (Fin n → ℝ)) (hA : ∀ i, LocallySemianalytic (A i)) :
    LocallySemianalytic (⋃ i, A i) := by
  simpa only [compl_iInter, compl_compl] using
    (LocallySemianalytic.iInter (fun i => (A i)ᶜ) (fun i => (hA i).compl)).compl

theorem LocallySemianalytic.preimage_analytic {n m : ℕ} {A : Set (Fin m → ℝ)}
    (hA : LocallySemianalytic A) (F : (Fin n → ℝ) → (Fin m → ℝ))
    (hF : ∀ x, AnalyticAt ℝ F x) : LocallySemianalytic (F ⁻¹' A) := by
  have hFc : Continuous F := continuous_iff_continuousAt.mpr (fun x => (hF x).continuousAt)
  intro x
  obtain ⟨O, hO, hxO, J, hJ, f, hf, Q, he⟩ := hA (F x)
  exact ⟨F ⁻¹' O, hO.preimage hFc, hxO, J, hJ, (fun j => f j ∘ F),
    (fun j y hy => (hf j (F y) hy).comp (hF y)), Q, fun y hy => he (F y) hy⟩

end PlanarNikodym
