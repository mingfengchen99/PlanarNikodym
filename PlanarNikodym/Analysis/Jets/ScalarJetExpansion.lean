import PlanarNikodym.Analysis.Jets.ScalarJetAmplitudes

/-! Finite scalar expansion of every actual auxiliary jet. Each term
retains its own compact real cutoff and the original oscillatory average. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace PlanarNikodym

def ScalarJetPath : ℕ → Type
  | 0 => Unit
  | j + 1 => ScalarJetPath j ⊕ ScalarJetPath j

instance scalarJetPathFintype (j : ℕ) : Fintype (ScalarJetPath j) := by
  induction j with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ j ih =>
    letI := ih
    exact inferInstanceAs (Fintype (ScalarJetPath j ⊕ ScalarJetPath j))

def scalarJetOrder : (j : ℕ) → ScalarJetPath j → ℕ
  | 0, _ => 0
  | j + 1, Sum.inl b => scalarJetOrder j b
  | j + 1, Sum.inr b => scalarJetOrder j b + 1

theorem scalarJetOrder_le (j : ℕ) (b : ScalarJetPath j) : scalarJetOrder j b ≤ j := by
  induction j with
  | zero => simp [scalarJetOrder]
  | succ j ih =>
    rcases b with b | b
    · exact (ih b).trans (Nat.le_succ j)
    · exact Nat.succ_le_succ (ih b)

def scalarJetVerticalIter (m : ℕ) (f : Plane → ℂ) : Plane → ℂ :=
  scalarJetVertical^[m] f

@[simp] theorem scalarJetVerticalIter_zero (f : Plane → ℂ) :
    scalarJetVerticalIter 0 f = f := rfl

@[simp] theorem scalarJetVerticalIter_succ (m : ℕ) (f : Plane → ℂ) :
    scalarJetVerticalIter (m + 1) f = scalarJetVertical (scalarJetVerticalIter m f) :=
  Function.iterate_succ_apply' _ _ _

theorem contDiff_scalarJetVerticalIter (m : ℕ) {f : Plane → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (scalarJetVerticalIter m f) := by
  induction m with
  | zero => exact hf
  | succ m ih => rw [scalarJetVerticalIter_succ]; exact contDiff_scalarJetVertical ih

/-- There are exactly two product/chain branches at each differentiation.
The coefficients are determined by geometry, cutoff and directions only. -/
def Family.scalarJetAmplitude {d : ℕ} (G : Family 2 d) (χ : Cutoff d) :
    (j : ℕ) → (Fin j → Aux d) → ScalarJetPath j → Cutoff d
  | 0, _, _ => χ
  | j + 1, v, Sum.inl b =>
      scalarJetCutoffDeriv (G.scalarJetAmplitude χ j (Fin.tail v) b) (0, v 0)
  | j + 1, v, Sum.inr b =>
      G.scalarJetPhaseCutoff (G.scalarJetAmplitude χ j (Fin.tail v) b) (0, v 0)

theorem Family.tsupport_scalarJetAmplitude_subset {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (j : ℕ) (v : Fin j → Aux d) (b : ScalarJetPath j) :
    tsupport (G.scalarJetAmplitude χ j v b) ⊆ tsupport χ := by
  induction j with
  | zero => exact Subset.rfl
  | succ j ih =>
    rcases b with b | b
    · exact (tsupport_scalarJetCutoffDeriv_subset _ _).trans (ih _ b)
    · exact (G.tsupport_scalarJetPhaseCutoff_subset _ _).trans (ih _ b)

theorem Family.contDiff_scalarJetAmplitude {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    (j : ℕ) (v : Fin j → Aux d) (b : ScalarJetPath j) :
    ContDiff ℝ ∞ (G.scalarJetAmplitude χ j v b) := by
  induction j with
  | zero => exact hχ
  | succ j ih =>
    rcases b with b | b
    · exact contDiff_scalarJetCutoffDeriv _ (ih _ b) _
    · exact G.contDiff_scalarJetPhaseCutoff _ (ih _ b)
        (fun x hx => hγ x (G.tsupport_scalarJetAmplitude_subset χ j _ b hx)) _

theorem Family.hasCompactSupport_scalarJetAmplitude {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hc : HasCompactSupport χ)
    (j : ℕ) (v : Fin j → Aux d) (b : ScalarJetPath j) :
    HasCompactSupport (G.scalarJetAmplitude χ j v b) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (G.tsupport_scalarJetAmplitude_subset χ j v b)

theorem Family.auxiliary_fderiv_cutoffAverage_scalarJet {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (z : Base 2) (u v : Aux d) :
    fderiv ℝ (fun w => G.cutoffAverage χ f (z, w)) u v =
      G.cutoffAverage (scalarJetCutoffDeriv χ (0, v)) f (z, u) +
      G.cutoffAverage (G.scalarJetPhaseCutoff χ (0, v)) (scalarJetVertical f) (z, u) := by
  rw [← G.fderiv_cutoffAverage_scalarJet χ hχ hc hγ hf (z, u) (0, v)]
  have h := ((G.cutoffAverage_contDiff χ hχ hc hγ hf).differentiable
    (by simp) (z, u)).hasFDerivAt.comp u
      ((hasFDerivAt_const z u).prodMk (hasFDerivAt_id u))
  exact congrArg (fun D : Aux d →L[ℝ] ℂ => D v) h.fderiv

/-- Exact finite expansion of the multilinear auxiliary jet, evaluated
on arbitrary directions. The finite amplitudes never depend on the input. -/
theorem Family.auxiliary_jet_eq_scalarJet_sum {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (j : ℕ)
    (z : Base 2) (u : Aux d) (v : Fin j → Aux d) :
    iteratedFDeriv ℝ j (fun w => G.cutoffAverage χ f (z, w)) u v =
      ∑ b : ScalarJetPath j, G.cutoffAverage (G.scalarJetAmplitude χ j v b)
        (scalarJetVerticalIter (scalarJetOrder j b) f) (z, u) := by
  have hA : ContDiff ℝ ∞ (fun w => G.cutoffAverage χ f (z, w)) :=
    (G.cutoffAverage_contDiff χ hχ hc hγ hf).comp (contDiff_const.prodMk contDiff_id)
  induction j generalizing u with
  | zero => simp [ScalarJetPath, scalarJetAmplitude, scalarJetOrder]
  | succ j ih =>
    have he : (fun w => iteratedFDeriv ℝ j (fun y => G.cutoffAverage χ f (z, y)) w
        (Fin.tail v)) = fun w => ∑ b : ScalarJetPath j,
          G.cutoffAverage (G.scalarJetAmplitude χ j (Fin.tail v) b)
            (scalarJetVerticalIter (scalarJetOrder j b) f) (z, w) := by
      funext w
      exact ih w (Fin.tail v)
    rw [iteratedFDeriv_succ_apply_left,
      ← fderiv_continuousMultilinear_apply_const_apply
        (hA.differentiable_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top j) u), he]
    rw [fderiv_fun_sum]
    · simp only [sum_apply]
      change (∑ b : ScalarJetPath j, _) = ∑ b : ScalarJetPath j ⊕ ScalarJetPath j, _
      rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      simpa only [scalarJetAmplitude, scalarJetOrder, scalarJetVerticalIter_succ] using
        G.auxiliary_fderiv_cutoffAverage_scalarJet (G.scalarJetAmplitude χ j (Fin.tail v) b)
        (G.contDiff_scalarJetAmplitude χ hχ hγ j _ b)
        (G.hasCompactSupport_scalarJetAmplitude χ hc j _ b)
        (fun x hx => hγ x (G.tsupport_scalarJetAmplitude_subset χ j _ b hx))
        (contDiff_scalarJetVerticalIter (scalarJetOrder j b) hf) z u (v 0)
    · intro b _
      exact ((G.cutoffAverage_contDiff _
        (G.contDiff_scalarJetAmplitude χ hχ hγ j _ b)
        (G.hasCompactSupport_scalarJetAmplitude χ hc j _ b)
        (fun x hx => hγ x (G.tsupport_scalarJetAmplitude_subset χ j _ b hx))
        (contDiff_scalarJetVerticalIter _ hf)).comp
        (contDiff_const.prodMk contDiff_id)).differentiable (by simp) u

end PlanarNikodym
