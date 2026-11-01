import PlanarNikodym.Classification.FullRankClassification
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Regular

/-! Actual averaging operators. Suprema take values in `ℝ≥0∞`, so an
unbounded supremum is not silently replaced by zero. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

abbrev Cutoff (d : ℕ) := ℝ × Parameters 2 d → ℝ

def Family.cutoffAverage {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (f : Plane → ℂ) (p : Parameters 2 d) : ℂ :=
  ∫ t : ℝ, (χ (t, p) : ℂ) * f (G.graphMap p t)

/-- Definition 2.2, with the pointwise (not essential) auxiliary supremum. -/
def Family.cutoffMaximal {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (f : Plane → ℂ) (z : Base 2) : ℝ≥0∞ :=
  ⨆ u : Aux d, ‖G.cutoffAverage χ f (z, u)‖ₑ

/-- Nonnegative time integral on the actual interval from Definition 1.3. -/
def Family.positiveAverage {d : ℕ} (G : Family 2 d)
    (f : Plane → ℝ≥0∞) (p : Parameters 2 d) : ℝ≥0∞ :=
  ∫⁻ t in G.I.carrier, f (G.graphMap p t)

def Family.positiveMaximal {d : ℕ} (G : Family 2 d)
    (U : Set (Parameters 2 d)) (f : Plane → ℝ≥0∞) (z : Base 2) : ℝ≥0∞ :=
  ⨆ u : Aux d, ⨆ (_ : (z, u) ∈ U), G.positiveAverage f (z, u)

theorem Family.positiveAverage_mono {d : ℕ} (G : Family 2 d)
    {f g : Plane → ℝ≥0∞} (h : f ≤ g) (p : Parameters 2 d) :
    G.positiveAverage f p ≤ G.positiveAverage g p :=
  lintegral_mono (fun t => h (G.graphMap p t))

theorem Family.positiveMaximal_mono {d : ℕ} (G : Family 2 d)
    {U V : Set (Parameters 2 d)} (hUV : U ⊆ V)
    {f g : Plane → ℝ≥0∞} (hfg : f ≤ g) :
    G.positiveMaximal U f ≤ G.positiveMaximal V g := by
  intro z
  exact iSup_le fun u => iSup_le fun hu => le_iSup_of_le u
    (le_iSup_of_le (hUV hu) (G.positiveAverage_mono hfg (z, u)))

theorem Family.positiveAverage_le_maximal {d : ℕ} (G : Family 2 d)
    {U : Set (Parameters 2 d)} (f : Plane → ℝ≥0∞)
    {z : Base 2} {u : Aux d} (hu : (z, u) ∈ U) :
    G.positiveAverage f (z, u) ≤ G.positiveMaximal U f z :=
  le_iSup_of_le u (le_iSup_of_le hu le_rfl)

@[simp] theorem Family.positiveMaximal_empty {d : ℕ} (G : Family 2 d)
    (f : Plane → ℝ≥0∞) : G.positiveMaximal ∅ f = 0 := by
  ext z
  simp [positiveMaximal]

theorem Family.positiveAverage_indicator {d : ℕ} (G : Family 2 d)
    (p : Parameters 2 d) (E : Set Plane)
    (hm : MeasurableSet (G.hitTimes p E)) :
    G.positiveAverage (E.indicator (fun _ => 1)) p = volume (G.hitTimes p E) := by
  classical
  have hI : MeasurableSet G.I.carrier := measurableSet_Icc
  rw [positiveAverage, ← lintegral_indicator hI]
  have he : G.I.carrier.indicator (fun t => E.indicator (fun _ => (1 : ℝ≥0∞))
      (G.graphMap p t)) = (G.hitTimes p E).indicator (fun _ => 1) := by
    ext t
    simp only [Family.hitTimes]
    by_cases ht : t ∈ G.I.carrier <;> by_cases hE : G.graphMap p t ∈ E <;>
      simp [ht, hE]
  rw [he, lintegral_indicator_const hm]
  simp

theorem Family.positiveAverage_iSup {d : ℕ} (G : Family 2 d)
    (f : ℕ → Plane → ℝ≥0∞)
    (p : Parameters 2 d)
    (hp : ∀ n, Measurable (fun t => f n (G.graphMap p t))) (hmono : Monotone f) :
    G.positiveAverage (fun x => ⨆ n, f n x) p = ⨆ n, G.positiveAverage (f n) p := by
  exact lintegral_iSup hp (fun i j hij t => hmono hij (G.graphMap p t))

/-- A concrete estimate for open-set indicators evaluated pointwise on
curves. No representative of an ambient `Lp` equivalence class is chosen. -/
def Family.OpenMaximalEstimate {d : ℕ} (G : Family 2 d)
    (U : Set (Parameters 2 d)) : Prop :=
  ∃ p : ℝ≥0, 1 ≤ p ∧ ∃ C : ℝ≥0,
    ∀ O : Set Plane, IsOpen O → volume O < ∞ →
      Measurable (G.positiveMaximal U (O.indicator (fun _ => 1))) ∧
      eLpNorm (G.positiveMaximal U (O.indicator (fun _ => 1))) p volume ≤
        C * (volume O) ^ (1 / (p : ℝ))

end PlanarNikodym
