import PlanarNikodym.Analysis.Maximal.E2SeeleySigmaCoefficients
import PlanarNikodym.Analysis.Maximal.E2SeeleyReflection
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Seeley's moment identities preserve full multilinear jets, including
all mixed time and parameter derivatives. -/
noncomputable section
open scoped BigOperators
namespace PlanarNikodym
variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem e2_multilinear_affine_expansion {m : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin m => V) F)
    (u v : Fin m → V) (b : ℝ) :
    A (fun j => b • u j + v j) =
      ∑ s : Finset (Fin m), b ^ s.card • A (s.piecewise u v) := by
  classical
  rw [show (fun j => b • u j + v j) = (fun j => b • u j) + v from rfl,
    A.map_add_univ]
  apply Finset.sum_congr rfl
  intro s _
  have hh : s.piecewise (fun j => b • u j) v =
      s.piecewise (fun j => b • s.piecewise u v j) (s.piecewise u v) := by
    funext j
    by_cases hj : j ∈ s <;> simp [hj]
  rw [hh, A.map_piecewise_smul]
  simp

theorem e2_multilinear_seeley_moment {m : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin m => V) F)
    (u v : Fin m → V) :
    ∑' i : E2SeeleyIndex, e2SeeleyA i • A (fun j => e2SeeleyB i • u j + v j) =
      A (u + v) := by
  classical
  have hs (s : Finset (Fin m)) :
      Summable (fun i : E2SeeleyIndex =>
        (e2SeeleyA i * e2SeeleyB i ^ s.card) • A (s.piecewise u v)) :=
    (e2Seeley_summable_moment s.card).smul_const _
  calc
    _ = ∑' i : E2SeeleyIndex, ∑ s : Finset (Fin m),
        (e2SeeleyA i * e2SeeleyB i ^ s.card) • A (s.piecewise u v) := by
      apply tsum_congr
      intro i
      rw [e2_multilinear_affine_expansion, Finset.smul_sum]
      simp only [smul_smul]
    _ = ∑ s : Finset (Fin m), ∑' i : E2SeeleyIndex,
        (e2SeeleyA i * e2SeeleyB i ^ s.card) • A (s.piecewise u v) :=
      Summable.tsum_finsetSum (fun s _ => hs s)
    _ = ∑ s : Finset (Fin m), A (s.piecewise u v) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [(e2Seeley_summable_moment s.card).tsum_smul_const,
        e2Seeley_moment, one_smul]
    _ = A (u + v) := (A.map_add_univ u v).symm


variable (V)

def e2NormalProjection : (ℝ × V) →L[ℝ] (ℝ × V) :=
  (ContinuousLinearMap.fst ℝ ℝ V).prod 0

def e2TangentialProjection : (ℝ × V) →L[ℝ] (ℝ × V) :=
  (0 : (ℝ × V) →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ V)

@[simp] theorem e2NormalTangential_eq (b : ℝ) :
    b • e2NormalProjection V + e2TangentialProjection V = e2TimeDilation V b := by
  ext x <;> simp [e2NormalProjection, e2TangentialProjection, e2TimeDilation]

variable {V}

theorem e2_seeley_full_jet_moment {m : ℕ}
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin m => ℝ × V) F) :
    ∑' i : E2SeeleyIndex, e2SeeleyA i •
      p.compContinuousLinearMap (fun _ => e2TimeDilation V (e2SeeleyB i)) = p := by
  let B := (ContinuousLinearMap.apply ℝ _ p).compContinuousMultilinearMap
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
      (fun _ : Fin m => ℝ × V) (fun _ : Fin m => ℝ × V) F)
  have hh := e2_multilinear_seeley_moment B
    (fun _ => e2NormalProjection V) (fun _ => e2TangentialProjection V)
  have hid : e2NormalProjection V + e2TangentialProjection V =
      ContinuousLinearMap.id ℝ (ℝ × V) := by
    ext x <;> simp [e2NormalProjection, e2TangentialProjection]
  have he (i : E2SeeleyIndex) :
      B (fun j => e2SeeleyB i • e2NormalProjection V + e2TangentialProjection V) =
        p.compContinuousLinearMap (fun _ => e2TimeDilation V (e2SeeleyB i)) := by
    simp only [e2NormalTangential_eq]
    rfl
  rw [tsum_congr (fun i => congrArg (fun q => e2SeeleyA i • q) (he i))] at hh
  convert hh using 1
  ext x
  change p x = p (fun j => (e2NormalProjection V + e2TangentialProjection V) (x j))
  rw [hid]
  rfl

end PlanarNikodym
