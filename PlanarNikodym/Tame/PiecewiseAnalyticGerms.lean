import PlanarNikodym.Geometry.SemianalyticGerms
import PlanarNikodym.Geometry.SemianalyticBasicSets

/-! Actual finite local analytic presentations, with semianalytic branch
regions. Composition retains the regions, including discontinuous branches. -/
noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A finite local presentation. Both branch regions and analytic formulas
are witnessed; no regularity is asserted across their boundaries. -/
def PiecewiseAnalyticAt {n : ℕ} (f : (Fin n → ℝ) → F) (a : Fin n → ℝ) : Prop :=
  ∃ (J : Type) (_ : Fintype J) (P : J → Set (Fin n → ℝ)) (g : J → (Fin n → ℝ) → F),
    (∀ j, SemianalyticAt (P j) a) ∧ (∀ j, AnalyticAt ℝ (g j) a) ∧
      ∀ᶠ x in 𝓝 a, (∃ j, x ∈ P j) ∧ ∀ j, x ∈ P j → f x = g j x

theorem AnalyticAt.piecewiseAnalyticAt {n : ℕ} {f : (Fin n → ℝ) → F}
    {a : Fin n → ℝ} (hf : AnalyticAt ℝ f a) : PiecewiseAnalyticAt f a := by
  refine ⟨Fin 1, inferInstance, (fun _ => univ), (fun _ => f), ?_, (fun _ => hf), ?_⟩
  · intro _
    exact ⟨univ, isOpen_univ, mem_univ _, Fin 0, inferInstance,
      (fun i => Fin.elim0 i), (fun i => Fin.elim0 i), (fun _ => True), fun _ _ => Iff.rfl⟩
  · exact Eventually.of_forall (fun _ => ⟨⟨0, mem_univ _⟩, fun _ _ => rfl⟩)

theorem PiecewiseAnalyticAt.congr {n : ℕ} {f g : (Fin n → ℝ) → F}
    {a : Fin n → ℝ} (hf : PiecewiseAnalyticAt f a) (he : f =ᶠ[𝓝 a] g) :
    PiecewiseAnalyticAt g a := by
  obtain ⟨J, hJ, P, u, hP, hu, hrep⟩ := hf
  refine ⟨J, hJ, P, u, hP, hu, ?_⟩
  filter_upwards [hrep, he] with x hx hxe
  exact ⟨hx.1, fun j hj => hxe.symm.trans (hx.2 j hj)⟩

theorem PiecewiseAnalyticAt.pi {n m : ℕ} {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {a : Fin n → ℝ} (hf : ∀ i, PiecewiseAnalyticAt (fun x => f x i) a) :
    PiecewiseAnalyticAt f a := by
  classical
  choose J hJ P g hP hg he using hf
  letI (i : Fin m) : Fintype (J i) := hJ i
  refine ⟨(i : Fin m) → J i, inferInstance,
    (fun j => ⋂ i, P i (j i)), (fun j x i => g i (j i) x), ?_, ?_, ?_⟩
  · intro j
    exact SemianalyticAt.iInter _ (fun i => hP i (j i))
  · intro j
    exact analyticAt_pi_iff.mpr (fun i => hg i (j i))
  · filter_upwards [Filter.eventually_all.mpr he] with x hx
    constructor
    · choose j hj using fun i => (hx i).1
      exact ⟨j, mem_iInter.mpr hj⟩
    · intro j hj
      exact funext (fun i => (hx i).2 (j i) (mem_iInter.mp hj i))

theorem PiecewiseAnalyticAt.comp {n m : ℕ} {f : (Fin m → ℝ) → F}
    {g : (Fin n → ℝ) → (Fin m → ℝ)} {a : Fin n → ℝ}
    (hf : ∀ b, PiecewiseAnalyticAt f b) (hg : PiecewiseAnalyticAt g a) :
    PiecewiseAnalyticAt (f ∘ g) a := by
  classical
  obtain ⟨J, hJ, P, u, hP, hu, he⟩ := hg
  choose K hK Q v hQ hv hr using fun j => hf (u j a)
  letI (j : J) : Fintype (K j) := hK j
  refine ⟨Σ j, K j, inferInstance,
    (fun j => P j.1 ∩ u j.1 ⁻¹' Q j.1 j.2),
    (fun j => v j.1 j.2 ∘ u j.1), ?_, ?_, ?_⟩
  · intro j
    exact (hP j.1).inter ((hQ j.1 j.2).preimage_analyticAt (u j.1) (hu j.1))
  · intro j
    exact (hv j.1 j.2).comp (hu j.1)
  · have hnear : ∀ᶠ x in 𝓝 a,
        ∀ j, (∃ k, u j x ∈ Q j k) ∧ ∀ k, u j x ∈ Q j k → f (u j x) = v j k (u j x) :=
      Filter.eventually_all.mpr (fun j => (hu j).continuousAt.eventually (hr j))
    filter_upwards [he, hnear] with x hx hxQ
    constructor
    · obtain ⟨j, hj⟩ := hx.1
      obtain ⟨k, hk⟩ := (hxQ j).1
      exact ⟨⟨j, k⟩, hj, hk⟩
    · intro j hj
      change f (g x) = v j.1 j.2 (u j.1 x)
      rw [hx.2 j.1 hj.1]
      exact (hxQ j.1).2 j.2 hj.2

theorem PiecewiseAnalyticAt.preimage {n m : ℕ} {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {a : Fin n → ℝ} (hf : PiecewiseAnalyticAt f a) {A : Set (Fin m → ℝ)}
    (hA : LocallySemianalytic A) : SemianalyticAt (f ⁻¹' A) a := by
  classical
  obtain ⟨J, hJ, P, g, hP, hg, he⟩ := hf
  have hlocal := SemianalyticAt.iUnion (fun j => P j ∩ g j ⁻¹' A)
    (fun j => (hP j).inter (SemianalyticAt.preimage_analyticAt (g j) (hA (g j a)) (hg j)))
  apply hlocal.congr
  filter_upwards [he] with x hx
  simp only [mem_iUnion, mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨j, hj, hgj⟩
    rwa [hx.2 j hj]
  · intro hfx
    obtain ⟨j, hj⟩ := hx.1
    exact ⟨j, hj, by rwa [← hx.2 j hj]⟩

end PlanarNikodym
