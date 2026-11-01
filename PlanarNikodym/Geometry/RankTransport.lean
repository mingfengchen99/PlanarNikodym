import PlanarNikodym.Geometry.LocalCoordinates
import PlanarNikodym.Geometry.AnalyticImplicit
import PlanarNikodym.Rank.Rank

noncomputable section
open Set Filter Submodule Module
open scoped Topology
namespace PlanarNikodym

theorem range_prod_decomposition {A B V : Type*}
    [AddCommGroup A] [Module ℝ A] [AddCommGroup B] [Module ℝ B]
    [AddCommGroup V] [Module ℝ V] (L : (A × B) →ₗ[ℝ] V) :
    L.range = (L.comp (LinearMap.inl ℝ A B)).range ⊔
      (L.comp (LinearMap.inr ℝ A B)).range := by
  apply le_antisymm
  · rintro v ⟨⟨a, b⟩, rfl⟩
    have he : L (a, b) = L (a, 0) + L (0, b) := by rw [← map_add]; simp
    rw [he]
    exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨a, rfl⟩)
      (Submodule.mem_sup_right ⟨b, rfl⟩)
  · apply sup_le
    · rintro v ⟨a, rfl⟩
      exact ⟨(a, 0), rfl⟩
    · rintro v ⟨b, rfl⟩
      exact ⟨(0, b), rfl⟩

theorem functionDerivative_snd_slice {X A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    (f : X → A × B → ℝ) (p : A × B) (hf : ∀ t, DifferentiableAt ℝ (f t) p) :
    functionDerivative (fun t b => f t (p.1, b)) p.2 =
      (functionDerivative f p).comp (ContinuousLinearMap.inr ℝ A B).toLinearMap := by
  ext b t
  exact congrArg (fun L : B →L[ℝ] ℝ => L b) (fderiv_snd_slice (f t) p (hf t))

theorem fderiv_fst_slice {A B F : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : A × B → F) (p : A × B) (hf : DifferentiableAt ℝ f p) :
    fderiv ℝ (fun a => f (a, p.2)) p.1 =
      (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ A B) := by
  have h : HasFDerivAt (fun a : A => (a, p.2)) (ContinuousLinearMap.inl ℝ A B) p.1 := by
    convert (hasFDerivAt_id (𝕜 := ℝ) p.1).prodMk
      (hasFDerivAt_const (𝕜 := ℝ) p.2 p.1) using 1 <;> rfl
  exact (hf.hasFDerivAt.comp p.1 h).fderiv

theorem functionDerivative_fst_slice {X A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    (f : X → A × B → ℝ) (p : A × B) (hf : ∀ t, DifferentiableAt ℝ (f t) p) :
    functionDerivative (fun t a => f t (a, p.2)) p.1 =
      (functionDerivative f p).comp (ContinuousLinearMap.inl ℝ A B).toLinearMap := by
  ext a t
  exact congrArg (fun L : A →L[ℝ] ℝ => L a) (fderiv_fst_slice (f t) p (hf t))

theorem Family.pointSpace_eq_range {d : ℕ} (G : Family 2 d) (p : Parameters 2 d) :
    G.pointSpace p = (functionDerivative (fun (t : G.I.carrier) u => G.γ t (p.1, u)) p.2).range := by
  rw [range_eq_span_coordinates]
  rfl

theorem Family.curveSpace_eq_range {d : ℕ} (G : Family 2 d) (p : Parameters 2 d)
    (hf : ∀ t : G.I.carrier, DifferentiableAt ℝ (G.γ t) p) :
    G.curveSpace p = (functionDerivative (fun (t : G.I.carrier) z => G.γ t z) p).range := by
  rw [Family.curveSpace, G.pointSpace_eq_range]
  have hz : span ℝ (range (G.zColumn p)) =
      (functionDerivative (fun (t : G.I.carrier) z => G.γ t (z, p.2)) p.1).range := by
    rw [range_eq_span_coordinates]
    rfl
  rw [hz, functionDerivative_snd_slice _ p hf, functionDerivative_fst_slice _ p hf,
    range_prod_decomposition, sup_comm]
  rfl

theorem functionDerivative_range_of_factorization {X E F B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (f : X → F → ℝ) (g : X → B → ℝ) (H : E → F) (P : E → B) (q : E)
    (hf : ∀ t, DifferentiableAt ℝ (f t) (H q))
    (hg : ∀ t, DifferentiableAt ℝ (g t) (P q))
    (hH : DifferentiableAt ℝ H q) (hP : DifferentiableAt ℝ P q)
    (sH : Function.Surjective (fderiv ℝ H q)) (sP : Function.Surjective (fderiv ℝ P q))
    (he : ∀ t, (fun x => f t (H x)) =ᶠ[𝓝 q] (fun x => g t (P x))) :
    (functionDerivative f (H q)).range = (functionDerivative g (P q)).range := by
  have hd : functionDerivative (fun t x => f t (H x)) q =
      functionDerivative (fun t x => g t (P x)) q := by
    ext k t
    exact congrArg (fun L : E →L[ℝ] ℝ => L k) ((he t).fderiv_eq (𝕜 := ℝ))
  rw [functionDerivative_comp f H q hf hH, functionDerivative_comp g P q hg hP] at hd
  have hr := congrArg LinearMap.range hd
  rwa [range_comp_eq_of_surjective _ _ sH, range_comp_eq_of_surjective _ _ sP] at hr

/-- The derivative of an analytic chart is invertible throughout its source. -/
theorem chart_fderiv_invertible {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph E E) (ha : AnalyticOnNhd ℝ e e.source)
    (hb : AnalyticOnNhd ℝ e.symm e.target) (p : E) (hp : p ∈ e.source) :
    (fderiv ℝ e p).IsInvertible := by
  have hf := (ha p hp).differentiableAt.hasFDerivAt
  have hg := (hb (e p) (e.map_source hp)).differentiableAt.hasFDerivAt
  have he : (fun x => e.symm (e x)) =ᶠ[𝓝 p] id :=
    (e.eventually_left_inverse hp)
  have h₁ := (hg.comp p hf).unique ((hasFDerivAt_id (𝕜 := ℝ) p).congr_of_eventuallyEq he)
  have he' := e.symm.eventually_left_inverse (e.map_source hp)
  have hf' : HasFDerivAt e (fderiv ℝ e p) (e.symm (e p)) := by
    simpa only [e.left_inv hp] using hf
  have hcomp : HasFDerivAt (fun y => e (e.symm y))
      ((fderiv ℝ e p).comp (fderiv ℝ e.symm (e p))) (e p) :=
    hf'.comp (e p) (f := fun y => e.symm y) hg
  have h₂ := hcomp.unique
    ((hasFDerivAt_id (𝕜 := ℝ) (e p)).congr_of_eventuallyEq he')
  exact ContinuousLinearMap.IsInvertible.of_inverse h₂ h₁

end PlanarNikodym
