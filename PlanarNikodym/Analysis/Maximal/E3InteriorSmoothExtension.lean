import PlanarNikodym.Analysis.Maximal.E3InteriorIntervals
import PlanarNikodym.Analysis.Fourier.GlyzLocalPhaseTransport
import PlanarNikodym.Geometry.CompactFiberNeighborhood

/-! Genuine global smooth phase replacements on compact interior time
intervals. The replacement is constructed before every frequency and
input, and preserves all actual cinematic derivatives. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PlanarNikodym

theorem Family.exists_e3_interior_smooth_extension {d : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W) (hG : G.IsSmooth) (i : InteriorIntervalIndex G.I)
    (q : Parameters 2 d) (hq : q ∈ G.W) :
    ∃ (U : Set (Parameters 2 d)) (H : Family 2 d),
      IsOpen U ∧ q ∈ U ∧ U ⊆ G.W ∧
      H.I = interiorInterval G.I i ∧ H.W = U ∧
      ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => H.γ x.1 x.2) ∧
      (∀ t ∈ (interiorInterval G.I i).carrier, ∀ p ∈ U, H.γ t p = G.γ t p) ∧
      (∀ x ∈ (interiorInterval G.I i).carrier ×ˢ U, H.cinematicDet x = G.cinematicDet x) := by
  let K := (interiorInterval G.I i).carrier ×ˢ ({q} : Set (Parameters 2 d))
  let O := Ioo G.I.left G.I.right ×ˢ G.W
  have hK : IsCompact K := isCompact_Icc.prod isCompact_singleton
  have hO : IsOpen O := isOpen_Ioo.prod hW
  have hKO : K ⊆ O := by
    rintro x ⟨ht, hp⟩
    have hpq : x.2 = q := mem_singleton_iff.mp hp
    exact ⟨interiorInterval_subset G.I i ht, hpq ▸ hq⟩
  obtain ⟨Ψ, N, hΨ, _, hN, hKN, _, heq⟩ := exists_compact_smooth_extension
    (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) hK hO hKO
    (fun x hx => G.contDiffAt_of_isSmooth_interior hW hG hx)
  have hlocal (t : ℝ) (ht : t ∈ (interiorInterval G.I i).carrier) :
      ∀ᶠ x : Parameters 2 d × ℝ in 𝓝 (q, t), (x.2, x.1) ∈ N :=
    continuous_swap.continuousAt.preimage_mem_nhds (hN.mem_nhds (hKN ⟨ht, mem_singleton q⟩))
  obtain ⟨V, hV, hqV, hVN⟩ := exists_open_nhds_compact_fiber_property
    (fun x : Parameters 2 d × ℝ => (x.2, x.1) ∈ N) q
    (interiorInterval G.I i).carrier isCompact_Icc hlocal
  let U := V ∩ G.W
  let H : Family 2 d :=
    { I := interiorInterval G.I i, W := U, γ := fun t p => Ψ (t, p) }
  refine ⟨U, H, hV.inter hW, ⟨hqV, hq⟩, inter_subset_right, rfl, rfl, hΨ, ?_, ?_⟩
  · intro t ht p hp
    exact heq (hVN p hp.1 t ht)
  · intro x hx
    apply H.cinematicDet_eq_of_eventuallyEq G
    filter_upwards [hN.mem_nhds (hVN x.2 hx.2.1 x.1 hx.1)] with y hy
    exact heq hy

end PlanarNikodym
