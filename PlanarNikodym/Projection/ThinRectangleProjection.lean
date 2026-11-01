import PlanarNikodym.Projection.ProjectionStationarity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Quantitative projection compression for thin neighbourhoods of segments.

This is the derivative form of the thin-rectangle estimate used in §2.1 of
Chang--Fraser--McDonald--Meyer--Taylor, arXiv:2609.31602v1. The estimates use the
ambient norm, so they apply directly to the max norm on `Plane`.
-/

noncomputable section
open Set MeasureTheory Metric
open scoped Topology

namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A closed segment of parameter length `ℓ`, thickened by vectors of norm at
most `w`. The direction need not be a unit vector. -/
def thinSegmentTube (p v : E) (ℓ w : ℝ) : Set E :=
  {q | ∃ t : ℝ, ∃ u : E, |t| ≤ ℓ / 2 ∧ ‖u‖ ≤ w ∧ q = p + t • v + u}

theorem thinSegmentTube_eq_image (p v : E) (ℓ w : ℝ) :
    thinSegmentTube p v ℓ w =
      (fun z : ℝ × E => p + z.1 • v + z.2) ''
        (Icc (-(ℓ / 2)) (ℓ / 2) ×ˢ closedBall (0 : E) w) := by
  ext q
  constructor
  · rintro ⟨t, u, ht, hu, hq⟩
    exact ⟨(t, u), ⟨abs_le.mp ht, by simpa using hu⟩, hq.symm⟩
  · rintro ⟨⟨t, u⟩, ⟨ht, hu⟩, hq⟩
    exact ⟨t, u, abs_le.mpr ht, by simpa using hu, hq.symm⟩

theorem isCompact_thinSegmentTube [ProperSpace E] (p v : E) (ℓ w : ℝ) :
    IsCompact (thinSegmentTube p v ℓ w) := by
  rw [thinSegmentTube_eq_image]
  exact (isCompact_Icc.prod (isCompact_closedBall _ _)).image
    ((continuous_const.add (continuous_fst.smul continuous_const)).add continuous_snd)

theorem isCompact_image_thinSegmentTube [ProperSpace E]
    {f : E → ℝ} {p v : E} {ℓ w : ℝ}
    (hf : ContinuousOn f (thinSegmentTube p v ℓ w)) :
    IsCompact (f '' thinSegmentTube p v ℓ w) :=
  (isCompact_thinSegmentTube p v ℓ w).image_of_continuousOn hf

theorem thinSegmentTube_norm_sub_le {p v q : E} {ℓ w : ℝ}
    (hq : q ∈ thinSegmentTube p v ℓ w) :
    ‖q - p‖ ≤ ℓ / 2 * ‖v‖ + w := by
  obtain ⟨t, u, ht, hu, rfl⟩ := hq
  calc
    ‖p + t • v + u - p‖ = ‖t • v + u‖ := by congr 1; abel
    _ ≤ ‖t • v‖ + ‖u‖ := norm_add_le _ _
    _ = |t| * ‖v‖ + ‖u‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ℓ / 2 * ‖v‖ + w := by
      gcongr

/-- Recentring at any point of a tube at most doubles both dimensions. This
allows a tangency witness in a descendant to control an ancestor tube. -/
theorem thinSegmentTube_subset_recenter {p v y : E} {ℓ w : ℝ}
    (hy : y ∈ thinSegmentTube p v ℓ w) :
    thinSegmentTube p v ℓ w ⊆ thinSegmentTube y v (2 * ℓ) (2 * w) := by
  obtain ⟨ty, uy, hty, huy, hyeq⟩ := hy
  rintro q ⟨t, u, ht, hu, hqeq⟩
  refine ⟨t - ty, u - uy, ?_, ?_, ?_⟩
  · have habs : |t - ty| ≤ |t| + |ty| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le t ty
    linarith
  · exact (norm_sub_le u uy).trans (by linarith)
  · rw [hyeq, hqeq, sub_smul]
    abel

/-- Taylor's mean value bound in a thin tube, retaining the small tangential
component of the actual linear approximation. -/
theorem norm_sub_le_of_mem_thinSegmentTube
    {f : E → ℝ} {S : Set E} {p v q : E} {ℓ w δ : ℝ}
    (A : E →L[ℝ] ℝ) (hδ : 0 ≤ δ) (hS : Convex ℝ S)
    (hf : ∀ z ∈ S, DifferentiableAt ℝ f z)
    (hder : ∀ z ∈ S, ‖fderiv ℝ f z - A‖ ≤ δ)
    (hp : p ∈ S) (hqS : q ∈ S) (hq : q ∈ thinSegmentTube p v ℓ w) :
    ‖f q - f p‖ ≤ (‖A v‖ + δ * ‖v‖) * (ℓ / 2) + (‖A‖ + δ) * w := by
  obtain ⟨t, u, ht, hu, hqeq⟩ := hq
  have hqp : q - p = t • v + u := by rw [hqeq]; abel
  have hlin : ‖A (q - p)‖ ≤ ℓ / 2 * ‖A v‖ + ‖A‖ * w := by
    rw [hqp, map_add, map_smul]
    calc
      ‖t • A v + A u‖ ≤ ‖t • A v‖ + ‖A u‖ := norm_add_le _ _
      _ ≤ |t| * ‖A v‖ + ‖A‖ * ‖u‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        gcongr
        exact A.le_opNorm u
      _ ≤ ℓ / 2 * ‖A v‖ + ‖A‖ * w := by gcongr
  have hdist : ‖q - p‖ ≤ ℓ / 2 * ‖v‖ + w :=
    thinSegmentTube_norm_sub_le ⟨t, u, ht, hu, hqeq⟩
  have herr := hS.norm_image_sub_le_of_norm_fderiv_le' hf hder hp hqS
  calc
    ‖f q - f p‖ ≤ ‖f q - f p - A (q - p)‖ + ‖A (q - p)‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ δ * (ℓ / 2 * ‖v‖ + w) + (ℓ / 2 * ‖A v‖ + ‖A‖ * w) := by
      exact add_le_add (herr.trans (mul_le_mul_of_nonneg_left hdist hδ)) hlin
    _ = (‖A v‖ + δ * ‖v‖) * (ℓ / 2) + (‖A‖ + δ) * w := by ring

/-- A genuine enclosing interval, derived from derivative bounds. -/
theorem image_thinSegmentTube_subset_Icc
    {f : E → ℝ} {S : Set E} {p v : E} {ℓ w δ : ℝ}
    (A : E →L[ℝ] ℝ) (hδ : 0 ≤ δ) (hS : Convex ℝ S)
    (hf : ∀ z ∈ S, DifferentiableAt ℝ f z)
    (hder : ∀ z ∈ S, ‖fderiv ℝ f z - A‖ ≤ δ)
    (hp : p ∈ S) (hTube : thinSegmentTube p v ℓ w ⊆ S) :
    f '' thinSegmentTube p v ℓ w ⊆
      Icc (f p - ((‖A v‖ + δ * ‖v‖) * (ℓ / 2) + (‖A‖ + δ) * w))
        (f p + ((‖A v‖ + δ * ‖v‖) * (ℓ / 2) + (‖A‖ + δ) * w)) := by
  rintro _ ⟨q, hq, rfl⟩
  have h := norm_sub_le_of_mem_thinSegmentTube A hδ hS hf hder hp (hTube hq) hq
  rw [Real.norm_eq_abs, abs_le] at h
  constructor <;> linarith

/-- Outer Lebesgue measure needs no separate measurability assumption on the
image. The bound comes from its enclosing interval. -/
theorem volume_image_thinSegmentTube_le
    {f : E → ℝ} {S : Set E} {p v : E} {ℓ w δ : ℝ}
    (A : E →L[ℝ] ℝ) (hδ : 0 ≤ δ) (hS : Convex ℝ S)
    (hf : ∀ z ∈ S, DifferentiableAt ℝ f z)
    (hder : ∀ z ∈ S, ‖fderiv ℝ f z - A‖ ≤ δ)
    (hp : p ∈ S) (hTube : thinSegmentTube p v ℓ w ⊆ S) :
    volume (f '' thinSegmentTube p v ℓ w) ≤
      ENNReal.ofReal ((‖A v‖ + δ * ‖v‖) * ℓ + 2 * (‖A‖ + δ) * w) := by
  refine (measure_mono
    (image_thinSegmentTube_subset_Icc A hδ hS hf hder hp hTube)).trans_eq ?_
  rw [Real.volume_Icc]
  congr 1
  ring

/-- Continuity of the actual derivative on a compact convex set gives a single
scale valid at every base point and for every tube contained in that set. -/
theorem exists_uniform_thinSegmentTube_projection_bound
    {f : E → ℝ} {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hf : ∀ z ∈ K, DifferentiableAt ℝ f z)
    (hcont : ContinuousOn (fderiv ℝ f) K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ ∀ p ∈ K, ∀ (v : E) (ℓ w : ℝ),
      ℓ / 2 * ‖v‖ + w ≤ r → thinSegmentTube p v ℓ w ⊆ K →
      volume (f '' thinSegmentTube p v ℓ w) ≤
        ENNReal.ofReal
          ((‖fderiv ℝ f p v‖ + δ * ‖v‖) * ℓ + 2 * (‖fderiv ℝ f p‖ + δ) * w) := by
  obtain ⟨r, hr, hmod⟩ :=
    Metric.uniformContinuousOn_iff_le.mp
      (hK.uniformContinuousOn_of_continuous hcont) δ hδ
  refine ⟨r, hr, ?_⟩
  intro p hp v ℓ w hsize hTube
  apply volume_image_thinSegmentTube_le (fderiv ℝ f p) hδ.le
    (hconv.inter (convex_closedBall p r))
  · intro z hz
    exact hf z hz.1
  · intro z hz
    simpa only [dist_eq_norm] using hmod z hz.1 p hp (by
      simpa only [mem_closedBall, dist_eq_norm] using hz.2)
  · exact ⟨hp, mem_closedBall_self hr.le⟩
  · intro q hq
    exact ⟨hTube hq, by
      rw [mem_closedBall, dist_eq_norm]
      exact (thinSegmentTube_norm_sub_le hq).trans hsize⟩

/-- Parameter-family version: compactness in both variables gives one scale
for every projection parameter. No differentiability in that parameter is
needed; the actual spatial derivatives must be jointly continuous. -/
theorem exists_uniform_family_thinSegmentTube_projection_bound
    {P : Type*} [PseudoMetricSpace P] {f : P → E → ℝ}
    {A : Set P} {K : Set E} (hA : IsCompact A) (hK : IsCompact K)
    (hconv : Convex ℝ K)
    (hf : ∀ a ∈ A, ∀ z ∈ K, DifferentiableAt ℝ (f a) z)
    (hcont : ContinuousOn (fun z : P × E => fderiv ℝ (f z.1) z.2) (A ×ˢ K))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ r > 0, ∀ a ∈ A, ∀ p ∈ K, ∀ (v : E) (ℓ w : ℝ),
      ℓ / 2 * ‖v‖ + w ≤ r → thinSegmentTube p v ℓ w ⊆ K →
      volume (f a '' thinSegmentTube p v ℓ w) ≤
        ENNReal.ofReal
          ((‖fderiv ℝ (f a) p v‖ + δ * ‖v‖) * ℓ +
            2 * (‖fderiv ℝ (f a) p‖ + δ) * w) := by
  obtain ⟨r, hr, hmod⟩ :=
    Metric.uniformContinuousOn_iff_le.mp
      ((hA.prod hK).uniformContinuousOn_of_continuous hcont) δ hδ
  refine ⟨r, hr, ?_⟩
  intro a ha p hp v ℓ w hsize hTube
  apply volume_image_thinSegmentTube_le (fderiv ℝ (f a) p) hδ.le
    (hconv.inter (convex_closedBall p r))
  · intro z hz
    exact hf a ha z hz.1
  · intro z hz
    have hd : dist (a, z) (a, p) ≤ r := by
      simpa using hz.2
    simpa only [dist_eq_norm] using hmod (a, z) ⟨ha, hz.1⟩ (a, p) ⟨ha, hp⟩ hd
  · exact ⟨hp, mem_closedBall_self hr.le⟩
  · intro q hq
    exact ⟨hTube hq, by
      rw [mem_closedBall, dist_eq_norm]
      exact (thinSegmentTube_norm_sub_le hq).trans hsize⟩

/-- Uniform thin-tube compression on a compact convex domain. Both the maximum
segment length and its positive relative thickness are constructed from the
continuous derivative. Near-tangency is measured by the actual derivative
`fderiv ℝ f p v`, rather than supplied image-measure bounds. -/
theorem exists_uniform_family_thinSegmentTube_compression
    {P : Type*} [PseudoMetricSpace P] {f : P → E → ℝ}
    {A : Set P} {K : Set E} (hA : IsCompact A) (hK : IsCompact K)
    (hconv : Convex ℝ K)
    (hf : ∀ a ∈ A, ∀ z ∈ K, DifferentiableAt ℝ (f a) z)
    (hcont : ContinuousOn (fun z : P × E => fderiv ℝ (f z.1) z.2) (A ×ˢ K))
    {V ε : ℝ} (hV : 0 ≤ V) (hε : 0 < ε) :
    ∃ r > 0, ∃ η > 0, ∀ a ∈ A, ∀ p ∈ K, ∀ (v : E) (ℓ : ℝ),
      ‖v‖ ≤ V → 0 ≤ ℓ → ℓ ≤ r → ‖fderiv ℝ (f a) p v‖ ≤ ε / 4 →
      thinSegmentTube p v ℓ (η * ℓ) ⊆ K →
      volume (f a '' thinSegmentTube p v ℓ (η * ℓ)) ≤ ENNReal.ofReal (ε * ℓ) := by
  obtain ⟨C, hC⟩ := (hA.prod hK).exists_bound_of_continuousOn hcont
  let M := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  have hMb (a : P) (ha : a ∈ A) (p : E) (hp : p ∈ K) :
      ‖fderiv ℝ (f a) p‖ ≤ M :=
    (hC (a, p) ⟨ha, hp⟩).trans (le_max_left _ _)
  let δ := ε / (4 * (V + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hVp : 0 < V + 1 := by positivity
  have hδeq : δ * (V + 1) = ε / 4 := by
    dsimp [δ]
    field_simp
  have hδV : δ * V ≤ ε / 4 := by nlinarith
  obtain ⟨r, hr, hbound⟩ :=
    exists_uniform_family_thinSegmentTube_projection_bound hA hK hconv hf hcont hδ
  let η := min (1 / 2 : ℝ) (ε / (4 * (M + δ + 1)))
  have hden : 0 < 4 * (M + δ + 1) := by positivity
  have hη : 0 < η := lt_min (by norm_num) (div_pos hε hden)
  have hηhalf : η ≤ 1 / 2 := min_le_left _ _
  have hηsmall : η * (4 * (M + δ + 1)) ≤ ε :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hηmass : 2 * (M + δ) * η ≤ ε / 2 := by nlinarith
  refine ⟨r / (V + 1), div_pos hr hVp, η, hη, ?_⟩
  intro a ha p hp v ℓ hv hℓ hℓr htan hTube
  have hsize : ℓ / 2 * ‖v‖ + η * ℓ ≤ r := by
    calc
      ℓ / 2 * ‖v‖ + η * ℓ ≤ ℓ / 2 * V + (1 / 2) * ℓ := by gcongr
      _ = ℓ * (V + 1) / 2 := by ring
      _ ≤ ℓ * (V + 1) := by nlinarith [mul_nonneg hℓ hVp.le]
      _ ≤ r := (le_div_iff₀ hVp).mp hℓr
  refine (hbound a ha p hp v ℓ (η * ℓ) hsize hTube).trans (ENNReal.ofReal_le_ofReal ?_)
  have htan' : ‖fderiv ℝ (f a) p v‖ + δ * ‖v‖ ≤ ε / 2 := by
    have : δ * ‖v‖ ≤ ε / 4 := (mul_le_mul_of_nonneg_left hv hδ.le).trans hδV
    linarith
  have hmass : 2 * (‖fderiv ℝ (f a) p‖ + δ) * η ≤ ε / 2 := by
    calc
      2 * (‖fderiv ℝ (f a) p‖ + δ) * η ≤ 2 * (M + δ) * η := by
        gcongr
        exact hMb a ha p hp
      _ ≤ ε / 2 := hηmass
  calc
    (‖fderiv ℝ (f a) p v‖ + δ * ‖v‖) * ℓ +
        2 * (‖fderiv ℝ (f a) p‖ + δ) * (η * ℓ) =
      (‖fderiv ℝ (f a) p v‖ + δ * ‖v‖) * ℓ +
        (2 * (‖fderiv ℝ (f a) p‖ + δ) * η) * ℓ := by ring
    _ ≤ (ε / 2) * ℓ + (ε / 2) * ℓ := by gcongr
    _ = ε * ℓ := by ring

theorem exists_uniform_thinSegmentTube_compression_of_norm_le
    {f : E → ℝ} {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hf : ∀ z ∈ K, DifferentiableAt ℝ f z)
    (hcont : ContinuousOn (fderiv ℝ f) K) {V ε : ℝ} (hV : 0 ≤ V) (hε : 0 < ε) :
    ∃ r > 0, ∃ η > 0, ∀ p ∈ K, ∀ (v : E) (ℓ : ℝ),
      ‖v‖ ≤ V → 0 ≤ ℓ → ℓ ≤ r → ‖fderiv ℝ f p v‖ ≤ ε / 4 →
      thinSegmentTube p v ℓ (η * ℓ) ⊆ K →
      volume (f '' thinSegmentTube p v ℓ (η * ℓ)) ≤ ENNReal.ofReal (ε * ℓ) := by
  obtain ⟨r, hr, η, hη, h⟩ := exists_uniform_family_thinSegmentTube_compression
    (f := fun _ : ℝ => f) (A := {0}) isCompact_singleton hK hconv
    (fun _ _ => hf)
    (hcont.comp continuousOn_snd (fun _ hz => hz.2)) hV hε
  exact ⟨r, hr, η, hη, h 0 rfl⟩

theorem exists_uniform_thinSegmentTube_compression
    {f : E → ℝ} {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hf : ∀ z ∈ K, DifferentiableAt ℝ f z)
    (hcont : ContinuousOn (fderiv ℝ f) K) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∃ η > 0, ∀ p ∈ K, ∀ (v : E) (ℓ : ℝ),
      ‖v‖ ≤ 1 → 0 ≤ ℓ → ℓ ≤ r → ‖fderiv ℝ f p v‖ ≤ ε / 4 →
      thinSegmentTube p v ℓ (η * ℓ) ⊆ K →
      volume (f '' thinSegmentTube p v ℓ (η * ℓ)) ≤ ENNReal.ofReal (ε * ℓ) :=
  exists_uniform_thinSegmentTube_compression_of_norm_le hK hconv hf hcont zero_le_one hε

/-- A tangency witness anywhere in the tube yields the same compression.
The derivative is evaluated at the actual witness `y`, not at the centre.
The doubled tube must stay inside the compact convex domain; in local
constructions this is supplied by a surrounding compact buffer. -/
theorem exists_uniform_family_thinSegmentTube_compression_of_witness
    {P : Type*} [PseudoMetricSpace P] {f : P → E → ℝ}
    {A : Set P} {K : Set E} (hA : IsCompact A) (hK : IsCompact K)
    (hconv : Convex ℝ K)
    (hf : ∀ a ∈ A, ∀ z ∈ K, DifferentiableAt ℝ (f a) z)
    (hcont : ContinuousOn (fun z : P × E => fderiv ℝ (f z.1) z.2) (A ×ˢ K))
    {V ε : ℝ} (hV : 0 ≤ V) (hε : 0 < ε) :
    ∃ r > 0, ∃ η > 0, ∀ a ∈ A, ∀ p y : E, ∀ (v : E) (ℓ : ℝ),
      y ∈ K → y ∈ thinSegmentTube p v ℓ (η * ℓ) →
      ‖v‖ ≤ V → 0 ≤ ℓ → ℓ ≤ r → ‖fderiv ℝ (f a) y v‖ ≤ ε / 8 →
      thinSegmentTube y v (2 * ℓ) (η * (2 * ℓ)) ⊆ K →
      volume (f a '' thinSegmentTube p v ℓ (η * ℓ)) ≤ ENNReal.ofReal (ε * ℓ) := by
  obtain ⟨r, hr, η, hη, h⟩ :=
    exists_uniform_family_thinSegmentTube_compression hA hK hconv hf hcont hV
      (show 0 < ε / 2 by positivity)
  refine ⟨r / 2, half_pos hr, η, hη, ?_⟩
  intro a ha p y v ℓ hyK hy hv hℓ hℓr htan hlarge
  have hsub : thinSegmentTube p v ℓ (η * ℓ) ⊆
      thinSegmentTube y v (2 * ℓ) (η * (2 * ℓ)) := by
    simpa only [show 2 * (η * ℓ) = η * (2 * ℓ) by ring] using
      thinSegmentTube_subset_recenter hy
  have hlargeBound := h a ha y hyK v (2 * ℓ) hv (by positivity)
    (by linarith) (by linarith) hlarge
  have hmeasure := (measure_mono (image_mono hsub)).trans hlargeBound
  simpa only [show ε / 2 * (2 * ℓ) = ε * ℓ by ring] using hmeasure

/-- The projective coordinate `s` represents the fiber direction `(-s,1)`. -/
theorem scalar_fderiv_slopeDirection
    {ψ : ℝ × Plane → ℝ} {p : ℝ × Plane}
    (hh : scalarHeadDerivative ψ p ≠ 0) (s : ℝ) :
    fderiv ℝ ψ p (0, (-s, 1)) =
      scalarHeadDerivative ψ p * (scalarGradientSlope ψ p - s) := by
  have hvec : ((0, (-s, 1)) : ℝ × Plane) =
      (-s) • (0, (1, 0)) + (0, (0, 1)) := by
    ext <;> simp
  rw [hvec, map_add, map_smul]
  change (-s) * scalarHeadDerivative ψ p + scalarTailDerivative ψ p = _
  dsimp only [scalarGradientSlope]
  field_simp
  ring

theorem norm_scalar_fderiv_slopeDirection
    {ψ : ℝ × Plane → ℝ} {p : ℝ × Plane}
    (hh : scalarHeadDerivative ψ p ≠ 0) (s : ℝ) :
    ‖fderiv ℝ ψ p (0, (-s, 1))‖ =
      |scalarHeadDerivative ψ p| * |scalarGradientSlope ψ p - s| := by
  rw [scalar_fderiv_slopeDirection hh, Real.norm_eq_abs, abs_mul]

/-- Actual spatial slice derivatives agree with the corresponding ambient
directional derivative, so slope separation can feed the tube estimate. -/
theorem scalar_slice_fderiv_slopeDirection
    {ψ : ℝ × Plane → ℝ} {p : ℝ × Plane}
    (hψ : DifferentiableAt ℝ ψ p) (hh : scalarHeadDerivative ψ p ≠ 0) (s : ℝ) :
    fderiv ℝ (fun q : Plane => ψ (p.1, q)) p.2 (-s, 1) =
      scalarHeadDerivative ψ p * (scalarGradientSlope ψ p - s) := by
  rw [fderiv_snd_slice ψ p hψ]
  exact scalar_fderiv_slopeDirection hh s

/-- Nearness to the actual fiber slope gives the small tangential derivative
needed in `exists_uniform_family_thinSegmentTube_projection_bound`. -/
theorem norm_scalar_slice_fderiv_slopeDirection_le
    {ψ : ℝ × Plane → ℝ} {p : ℝ × Plane} {s M δ : ℝ}
    (hψ : DifferentiableAt ℝ ψ p) (hh : scalarHeadDerivative ψ p ≠ 0)
    (hhead : |scalarHeadDerivative ψ p| ≤ M)
    (hslope : |scalarGradientSlope ψ p - s| ≤ δ) :
    ‖fderiv ℝ (fun q : Plane => ψ (p.1, q)) p.2 (-s, 1)‖ ≤ M * δ := by
  rw [scalar_slice_fderiv_slopeDirection hψ hh, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul hhead hslope (abs_nonneg _) ((abs_nonneg _).trans hhead)

/-- Joint continuity of ambient derivatives supplies joint continuity of the
actual spatial derivatives required by the parameter-family estimate. -/
theorem continuousOn_scalarSlice_fderiv
    {ψ : ℝ × Plane → ℝ} {S : Set (ℝ × Plane)}
    (hψ : ∀ p ∈ S, DifferentiableAt ℝ ψ p)
    (hcont : ContinuousOn (fderiv ℝ ψ) S) :
    ContinuousOn
      (fun p : ℝ × Plane => fderiv ℝ (fun q : Plane => ψ (p.1, q)) p.2) S := by
  apply (hcont.clm_comp
    (continuousOn_const (c := ContinuousLinearMap.inr ℝ ℝ Plane))).congr
  intro p hp
  exact fderiv_snd_slice ψ p (hψ p hp)

theorem continuousOn_scalarSlice_fderiv_of_analyticOnNhd
    {ψ : ℝ × Plane → ℝ} {S : Set (ℝ × Plane)}
    (hψ : AnalyticOnNhd ℝ ψ S) :
    ContinuousOn
      (fun p : ℝ × Plane => fderiv ℝ (fun q : Plane => ψ (p.1, q)) p.2) S :=
  continuousOn_scalarSlice_fderiv
    (fun p hp => (hψ p hp).differentiableAt)
    (fun p hp => (hψ p hp).fderiv.continuousAt.continuousWithinAt)

end PlanarNikodym
