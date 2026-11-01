import PlanarNikodym.Geometry.SemianalyticOperations

/-! Pointwise semianalytic germs and genuine analytic inverse images.
These are local versions of the existing analytic-sign definition. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace PlanarNikodym

abbrev SemianalyticAt {n : ℕ} (A : Set (Fin n → ℝ)) (a : Fin n → ℝ) : Prop :=
  ∃ O : Set (Fin n → ℝ), IsOpen O ∧ a ∈ O ∧
    ∃ (J : Type) (_ : Fintype J) (f : J → (Fin n → ℝ) → ℝ),
      (∀ j, AnalyticOnNhd ℝ (f j) O) ∧ ∃ Q : (J → Fin 3) → Prop,
        ∀ y ∈ O, y ∈ A ↔ Q (fun j => oneDimensionalSign (f j y))

theorem SemianalyticAt.congr {n : ℕ} {A B : Set (Fin n → ℝ)} {a : Fin n → ℝ}
    (hA : SemianalyticAt A a) (he : ∀ᶠ x in 𝓝 a, x ∈ A ↔ x ∈ B) :
    SemianalyticAt B a := by
  obtain ⟨O, hO, ha, J, hJ, f, hf, Q, hrep⟩ := hA
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp he
  exact ⟨O ∩ ball a r, hO.inter isOpen_ball, ⟨ha, mem_ball_self hr⟩,
    J, hJ, f, (fun j => (hf j).mono inter_subset_left), Q,
    fun x hx => (hsub hx.2).symm.trans (hrep x hx.1)⟩

theorem SemianalyticAt.compl {n : ℕ} {A : Set (Fin n → ℝ)} {a : Fin n → ℝ}
    (hA : SemianalyticAt A a) : SemianalyticAt Aᶜ a := by
  obtain ⟨O, hO, ha, J, hJ, f, hf, Q, hrep⟩ := hA
  exact ⟨O, hO, ha, J, hJ, f, hf, (fun s => ¬ Q s), fun y hy => (hrep y hy).not⟩

theorem SemianalyticAt.inter {n : ℕ} {A B : Set (Fin n → ℝ)} {a : Fin n → ℝ}
    (hA : SemianalyticAt A a) (hB : SemianalyticAt B a) :
    SemianalyticAt (A ∩ B) a := by
  obtain ⟨O, hO, haO, J, hJ, f, hf, Q, he⟩ := hA
  obtain ⟨V, hV, haV, K, hK, g, hg, R, hr⟩ := hB
  refine ⟨O ∩ V, hO.inter hV, ⟨haO, haV⟩, J ⊕ K, inferInstance, Sum.elim f g, ?_,
    (fun s => Q (fun j => s (Sum.inl j)) ∧ R (fun k => s (Sum.inr k))), ?_⟩
  · rintro (j | k) y hy
    · exact hf j y hy.1
    · exact hg k y hy.2
  · intro y hy
    exact (he y hy.1).and (hr y hy.2)

theorem SemianalyticAt.iInter {n : ℕ} {ι : Type} [Fintype ι]
    (A : ι → Set (Fin n → ℝ)) {a : Fin n → ℝ} (hA : ∀ i, SemianalyticAt (A i) a) :
    SemianalyticAt (⋂ i, A i) a := by
  classical
  choose O hO haO J hJ f hf Q he using hA
  letI (i : ι) : Fintype (J i) := hJ i
  refine ⟨⋂ i, O i, isOpen_iInter_of_finite hO, mem_iInter.mpr haO,
    Σ i, J i, inferInstance, (fun j => f j.1 j.2), ?_,
    (fun s => ∀ i, Q i (fun j => s ⟨i, j⟩)), ?_⟩
  · intro j y hy
    exact hf j.1 j.2 y (mem_iInter.mp hy j.1)
  · intro y hy
    simp only [mem_iInter]
    exact forall_congr' (fun i => he i y (mem_iInter.mp hy i))

theorem SemianalyticAt.iUnion {n : ℕ} {ι : Type} [Fintype ι]
    (A : ι → Set (Fin n → ℝ)) {a : Fin n → ℝ} (hA : ∀ i, SemianalyticAt (A i) a) :
    SemianalyticAt (⋃ i, A i) a := by
  simpa only [compl_iInter, compl_compl] using
    (SemianalyticAt.iInter (fun i => (A i)ᶜ) (fun i => (hA i).compl)).compl

theorem SemianalyticAt.preimage_analyticAt {n m : ℕ} {A : Set (Fin m → ℝ)}
    (F : (Fin n → ℝ) → (Fin m → ℝ)) {a : Fin n → ℝ}
    (hA : SemianalyticAt A (F a)) (hF : AnalyticAt ℝ F a) :
    SemianalyticAt (F ⁻¹' A) a := by
  obtain ⟨O, hO, haO, J, hJ, f, hf, Q, he⟩ := hA
  have hnear : {y | F y ∈ O ∧ AnalyticAt ℝ F y} ∈ 𝓝 a :=
    inter_mem (hF.continuousAt.preimage_mem_nhds (hO.mem_nhds haO)) hF.eventually_analyticAt
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hnear
  exact ⟨ball a r, isOpen_ball, mem_ball_self hr, J, hJ, (fun j => f j ∘ F),
    (fun j y hy => (hf j (F y) (hsub hy).1).comp (hsub hy).2), Q,
    fun y hy => he (F y) (hsub hy).1⟩

theorem semianalyticAt_of_analytic_sign_germs {n : ℕ} {J : Type} [Fintype J]
    (f : J → (Fin n → ℝ) → ℝ) {a : Fin n → ℝ} (hf : ∀ j, AnalyticAt ℝ (f j) a)
    (Q : (J → Fin 3) → Prop) :
    SemianalyticAt {x | Q (fun j => oneDimensionalSign (f j x))} a := by
  have hnear : {x | ∀ j, AnalyticAt ℝ (f j) x} ∈ 𝓝 a :=
    Filter.eventually_all.mpr (fun j => (hf j).eventually_analyticAt)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hnear
  exact ⟨ball a r, isOpen_ball, mem_ball_self hr, J, inferInstance, f,
    (fun j x hx => hsub hx j), Q, fun _ _ => Iff.rfl⟩

end PlanarNikodym
