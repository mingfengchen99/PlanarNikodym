import PlanarNikodym.Rank.GenericAnalyticRank
import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.Baire.Lemmas

/-! Common nonflat directions for finite analytic germ families. A nonzero
Taylor diagonal is selected from the actual convergent expansion, so no
symmetry or polarization certificate is postulated. Finite dense open
nonvanishing loci then give one direction for the entire family. -/
noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonzero analytic germ has an actual nonzero homogeneous Taylor diagonal. -/
theorem exists_nonzero_analytic_taylor_diagonal {f : E → ℝ} {x : E}
    (ha : AnalyticAt ℝ f x) (hn : ¬ ∀ᶠ y in 𝓝 x, f y = 0) :
    ∃ p : FormalMultilinearSeries ℝ E ℝ, HasFPowerSeriesAt f p x ∧
      ∃ (m : ℕ) (v : E), p m (fun _ => v) ≠ 0 := by
  obtain ⟨p, r, hp⟩ := ha
  refine ⟨p, ⟨r, hp⟩, ?_⟩
  by_contra! hz
  apply hn
  filter_upwards [Metric.eball_mem_nhds x hp.r_pos] with y hy
  have hy' : y - x ∈ Metric.eball (0 : E) r := by
    simpa only [Metric.mem_eball, edist_eq_enorm_sub, sub_zero] using hy
  have hs := hp.hasSum hy'
  have hs0 : HasSum (fun _ : ℕ => (0 : ℝ)) (f y) := by
    simpa only [hz, add_sub_cancel] using hs
  exact hs0.unique hasSum_zero

/-- A nonzero Taylor diagonal prevents the actual line restriction from being
locally zero, by uniqueness of the real one-variable power series. -/
theorem nonflat_line_of_nonzero_taylor_diagonal {f : E → ℝ} {x : E}
    {p : FormalMultilinearSeries ℝ E ℝ} (hp : HasFPowerSeriesAt f p x)
    (m : ℕ) (v : E) (hn : p m (fun _ => v) ≠ 0) :
    AnalyticAt ℝ (fun t : ℝ => f (x + t • v)) 0 ∧
      ¬ ∀ᶠ t : ℝ in 𝓝 0, f (x + t • v) = 0 := by
  let u : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have hu (t : ℝ) : u t = t • v := rfl
  have hp0 : HasFPowerSeriesAt (fun y => f (x + y)) p (0 : E) := by
    simpa only [add_neg_cancel, sub_neg_eq_add, add_comm] using hp.comp_sub (-x)
  have hline : HasFPowerSeriesAt (fun t : ℝ => f (x + t • v))
      (p.compContinuousLinearMap u) 0 := by
    simpa only [Function.comp_def, hu] using
      (show HasFPowerSeriesAt (fun y => f (x + y)) p (u 0) by
        simpa only [map_zero] using hp0).compContinuousLinearMap
  refine ⟨hline.analyticAt, ?_⟩
  intro hz
  have he := hline.eq_zero_of_eventually hz
  have hm := congrArg (fun q : FormalMultilinearSeries ℝ ℝ ℝ => q m (fun _ => 1)) he
  apply hn
  change (p m) (fun _ => u 1) = 0 at hm
  simpa only [hu, one_smul] using hm

/-- A finite collection of nonzero analytic germs admits one common nonzero
line direction, with analytic and nonflat restrictions for every member. -/
theorem exists_common_nonflat_analytic_direction [Nontrivial E]
    {J : Type*} [Fintype J] (f : J → E → ℝ) (x : E)
    (ha : ∀ j, AnalyticAt ℝ (f j) x)
    (hn : ∀ j, ¬ ∀ᶠ y in 𝓝 x, f j y = 0) :
    ∃ v : E, v ≠ 0 ∧ ∀ j,
      AnalyticAt ℝ (fun t : ℝ => f j (x + t • v)) 0 ∧
        ¬ ∀ᶠ t : ℝ in 𝓝 0, f j (x + t • v) = 0 := by
  classical
  choose p hp m w hw using fun j => exists_nonzero_analytic_taylor_diagonal (ha j) (hn j)
  let H (j : J) (v : E) := p j (m j) (fun _ => v)
  have hH (j : J) : AnalyticOnNhd ℝ (H j) univ := by
    intro v _
    exact (p j (m j)).analyticAt.comp (analyticAt_pi_iff.mpr (fun _ => analyticAt_id))
  let D (j : J) := {v : E | H j v ≠ 0}
  have hD (j : J) : IsOpen (D j) ∧ Dense (D j) := by
    obtain ⟨ho, hd⟩ := analytic_nonzero_locus univ isOpen_univ isPreconnected_univ
      (H j) (hH j) (w j) (mem_univ _) (hw j)
    simpa only [mem_univ, true_and] using
      (show IsOpen {v | v ∈ univ ∧ H j v ≠ 0} ∧ Dense {v | v ∈ univ ∧ H j v ≠ 0} from
        ⟨ho, fun v => hd (mem_univ v)⟩)
  have hdense : Dense (⋂ j, D j) := by
    rw [← sInter_range]
    exact (Set.finite_range D).dense_sInter
      (by rintro _ ⟨j, rfl⟩; exact (hD j).1)
      (by rintro _ ⟨j, rfl⟩; exact (hD j).2)
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : E)
  obtain ⟨v, hv0, hv⟩ := hdense.inter_open_nonempty ({(0 : E)}ᶜ) isOpen_compl_singleton
    ⟨v₀, by simpa only [mem_compl_iff, mem_singleton_iff] using hv₀⟩
  refine ⟨v, by simpa only [mem_compl_iff, mem_singleton_iff] using hv0, ?_⟩
  intro j
  exact nonflat_line_of_nonzero_taylor_diagonal (hp j) (m j) v (mem_iInter.mp hv j)

end PlanarNikodym
