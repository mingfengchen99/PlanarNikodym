import PlanarNikodym.Reduction.ParameterReduction

noncomputable section
open Set Filter Submodule Module
open scoped Topology ContDiff Matrix
namespace PlanarNikodym

theorem compensated_analyticAt {a b c : ℕ} (κ : BlockParameters a b c → Aux b)
    (p : BlockParameters a b c) (hκ : AnalyticAt ℝ κ p) :
    AnalyticAt ℝ (compensated κ) p := by
  exact ((analyticAt_fst.comp analyticAt_fst).prod hκ).prod analyticAt_snd

theorem compensator_det_near {X : Type*} {a b c : ℕ}
    (φ : X → BlockParameters a b c → ℝ) (x : Fin b → X)
    (κ : BlockParameters a b c → Aux b) (q : BlockParameters a b c)
    (hf : ∀ i, AnalyticAt ℝ (φ (x i)) q) (hκ : AnalyticAt ℝ κ q) (hκq : κ q = q.1.2)
    (hdet : Matrix.det (fun i j => wDerivative φ q (Pi.single j 1) (x i)) ≠ 0) :
    ∀ᶠ p in 𝓝 q,
      Matrix.det (fun i j => wDerivative φ (compensated κ p) (Pi.single j 1) (x i)) ≠ 0 := by
  have hFq : compensated κ q = q := by simp [compensated, hκq]
  have he : ∀ i j, AnalyticAt ℝ
      (fun p => wDerivative φ p (Pi.single j 1) (x i)) q := by
    intro i j
    have hv : AnalyticAt ℝ (fun L : BlockParameters a b c →L[ℝ] ℝ =>
        L (wIn a b c (Pi.single j 1))) (fderiv ℝ (φ (x i)) q) :=
      (ContinuousLinearMap.apply ℝ ℝ (wIn a b c (Pi.single j 1))).analyticAt _
    exact hv.comp (hf i).fderiv
  have hd := (analyticAt_det he).continuousAt.eventually_ne hdet
  have ht := (compensated_analyticAt κ q hκ).continuousAt.tendsto
  rw [hFq] at ht
  exact ht hd

theorem compensated_eta_derivative_zero {X : Type*} {a b c : ℕ}
    (φ : X → BlockParameters a b c → ℝ) (κ : BlockParameters a b c → Aux b)
    (η₀ : Aux c) (U : Set (BlockParameters a b c)) (hU : IsOpen U)
    (p : BlockParameters a b c) (hp : p ∈ U) (x : Fin b → X)
    (hκ : AnalyticAt ℝ κ p)
    (hf : ∀ t, DifferentiableAt ℝ (φ t) (compensated κ p))
    (hr : BlockRank φ (compensated κ p))
    (hdet : Matrix.det (fun i j => wDerivative φ (compensated κ p) (Pi.single j 1) (x i)) ≠ 0)
    (heq : ∀ z ∈ U, ∀ i, φ (x i) (compensated κ z) = φ (x i) (z.1, η₀)) :
    ∀ t, fderiv ℝ (fun η => φ t (compensated κ (p.1, η))) p.2 = 0 := by
  let K : Aux c →L[ℝ] BlockParameters a b c :=
    ((0 : Aux c →L[ℝ] Aux a).prod ((fderiv ℝ κ p).comp (etaIn a b c))).prod
      (ContinuousLinearMap.id ℝ (Aux c))
  have hInsert : HasFDerivAt (fun η : Aux c => (p.1, η)) (etaIn a b c) p.2 := by
    convert (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) p.2) using 1 <;> rfl
  have hF : HasFDerivAt (fun η => compensated κ (p.1, η)) K p.2 := by
    exact ((hasFDerivAt_const (𝕜 := ℝ) p.1.1 p.2).prodMk
      (hκ.differentiableAt.hasFDerivAt.comp p.2 hInsert)).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) p.2)
  have hψ (t : X) : HasFDerivAt (fun η => φ t (compensated κ (p.1, η)))
      ((fderiv ℝ (φ t) (compensated κ p)).comp K) p.2 :=
    (hf t).hasFDerivAt.comp p.2 (f := fun η => compensated κ (p.1, η)) hF
  have hEval : ∀ δ i, fderiv ℝ (φ (x i)) (compensated κ p) (K δ) = 0 := by
    intro δ i
    have he : (fun η => φ (x i) (compensated κ (p.1, η))) =ᶠ[𝓝 p.2]
        (fun _ => φ (x i) (p.1, η₀)) := by
      have hn := hInsert.continuousAt.preimage_mem_nhds (hU.mem_nhds hp)
      filter_upwards [hn] with η hη
      exact heq (p.1, η) hη i
    have hz := (hasFDerivAt_const (𝕜 := ℝ) (φ (x i) (p.1, η₀)) p.2).congr_of_eventuallyEq he
    exact congrArg (fun L : Aux c →L[ℝ] ℝ => L δ) ((hψ (x i)).unique hz)
  intro t
  rw [(hψ t).fderiv]
  ext δ
  exact block_eval_kernel φ (compensated κ p) (K δ) hr x hdet rfl (hEval δ) t

/-- Normalization on the base slice makes the triangular compensation map locally invertible. -/
theorem compensated_isInvertible {a b c : ℕ} (κ : BlockParameters a b c → Aux b)
    (q : BlockParameters a b c) (hκ : AnalyticAt ℝ κ q)
    (hnorm : ∀ᶠ v in 𝓝 q.1, κ (v, q.2) = v.2) :
    (fderiv ℝ (compensated κ) q).IsInvertible := by
  let F := compensated κ
  let D := fderiv ℝ F q
  have hF := (compensated_analyticAt κ q hκ).differentiableAt.hasFDerivAt
  have hs : (ContinuousLinearMap.snd ℝ (Aux a × Aux b) (Aux c)).comp D =
      ContinuousLinearMap.snd ℝ (Aux a × Aux b) (Aux c) := hF.snd.unique hasFDerivAt_snd
  have hInsert : HasFDerivAt (fun v : Aux a × Aux b => (v, q.2))
      (ContinuousLinearMap.inl ℝ (Aux a × Aux b) (Aux c)) q.1 := by
    convert (hasFDerivAt_id (𝕜 := ℝ) q.1).prodMk
      (hasFDerivAt_const (𝕜 := ℝ) q.2 q.1) using 1 <;> rfl
  have he : (fun v => F (v, q.2)) =ᶠ[𝓝 q.1] (fun v => (v, q.2)) := by
    filter_upwards [hnorm] with v hv
    simp [F, compensated, hv]
  have hc : HasFDerivAt (fun v => F (v, q.2))
      (D.comp (ContinuousLinearMap.inl ℝ (Aux a × Aux b) (Aux c))) q.1 :=
    hF.comp q.1 (f := fun v : Aux a × Aux b => (v, q.2)) hInsert
  have hbase : HasFDerivAt (fun v => F (v, q.2))
      (ContinuousLinearMap.inl ℝ (Aux a × Aux b) (Aux c)) q.1 :=
    hInsert.congr_of_eventuallyEq he
  have hd := hc.unique hbase
  have hinj : Function.Injective D := by
    apply (injective_iff_map_eq_zero D).mpr
    intro k hk
    have hk2 : k.2 = 0 := by
      have hh := congrArg (fun L : BlockParameters a b c →L[ℝ] Aux c => L k) hs
      simpa [hk] using hh.symm
    have hkD := congrArg (fun L : (Aux a × Aux b) →L[ℝ] BlockParameters a b c => L k.1) hd
    have hdk : D (k.1, 0) = (k.1, 0) := hkD
    have hkk : (k.1, (0 : Aux c)) = k := Prod.ext rfl hk2.symm
    rw [hkk, hk] at hdk
    exact hdk.symm
  exact ⟨(LinearEquiv.ofBijective D.toLinearMap
    ⟨hinj, LinearMap.surjective_of_injective hinj⟩).toContinuousLinearEquiv, rfl⟩

end PlanarNikodym
