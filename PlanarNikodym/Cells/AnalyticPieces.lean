import PlanarNikodym.Classification.ReuseLocalization
import PlanarNikodym.Core.Statements

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace PlanarNikodym

/-- A centre-preserving analytic parametrization of a possibly lower
dimensional piece. The inverse is continuous on the image, not on an
incorrectly assumed ambient-open target of the original dimension. -/
structure AnalyticPiece {d : ℕ} (G : Family 2 d) where
  dim : ℕ
  dim_le : dim ≤ d
  family : Family 2 dim
  interval_eq : family.I = G.I
  open_domain : IsOpen family.W
  bounded_domain : Bornology.IsBounded family.W
  connected_domain : IsConnected family.W
  analytic_family : family.IsAnalytic
  embed : Parameters 2 dim → Parameters 2 d
  inverse : Parameters 2 d → Parameters 2 dim
  analytic_embed : AnalyticOnNhd ℝ embed family.W
  continuous_inverse : ContinuousOn inverse (embed '' family.W)
  left_inv : ∀ p ∈ family.W, inverse (embed p) = p
  keep_center : ∀ p ∈ family.W, (embed p).1 = p.1
  maps_to : ∀ p ∈ family.W, embed p ∈ G.W
  identity : ∀ p ∈ family.W, ∀ t ∈ G.I.carrier, family.γ t p = G.γ t (embed p)

namespace AnalyticPiece
variable {d : ℕ} {G : Family 2 d} (P : AnalyticPiece G)

def restrict (G : Family 2 d) (U : Set (Parameters 2 d)) (ho : IsOpen U)
    (hb : Bornology.IsBounded U) (hc : IsConnected U) (ha : (G.restrictTo U).IsAnalytic)
    (hUW : U ⊆ G.W) : AnalyticPiece G where
  dim := d
  dim_le := le_rfl
  family := G.restrictTo U
  interval_eq := rfl
  open_domain := ho
  bounded_domain := hb
  connected_domain := hc
  analytic_family := ha
  embed := id
  inverse := id
  analytic_embed := fun _ _ => analyticAt_id
  continuous_inverse := continuousOn_id
  left_inv := fun _ _ => rfl
  keep_center := fun _ _ => rfl
  maps_to := fun _ hp => hUW hp
  identity := fun _ _ _ _ => rfl

def image : Set (Parameters 2 d) := P.embed '' P.family.W

theorem image_subset : P.image ⊆ G.W := by
  rintro _ ⟨p, hp, rfl⟩
  exact P.maps_to p hp

theorem embed_injOn : InjOn P.embed P.family.W := by
  intro p hp q hq he
  simpa only [P.left_inv p hp, P.left_inv q hq] using congrArg P.inverse he

theorem curve_eq (p : Parameters 2 P.dim) (hp : p ∈ P.family.W) :
    P.family.curve p = G.curve (P.embed p) := by
  have hi : P.family.I.carrier = G.I.carrier := congrArg Interval.carrier P.interval_eq
  unfold Family.curve
  rw [hi]
  apply image_congr
  intro t ht
  exact Prod.ext rfl (P.identity p hp t ht)

theorem curves_mono (z : Base 2) : P.family.curvesAtOn P.family.W z ⊆ G.curvesAtOn G.W z := by
  rintro β ⟨u, hu, he⟩
  have hc := P.curve_eq (z, u) hu
  have hz := P.keep_center (z, u) hu
  have hparam : P.embed (z, u) = (z, (P.embed (z, u)).2) := Prod.ext hz rfl
  refine ⟨(P.embed (z, u)).2, ?_, ?_⟩
  · exact hparam ▸ P.maps_to (z, u) hu
  · have hβ : G.curve (P.embed (z, u)) = β := hc.symm.trans he
    exact hparam ▸ hβ

theorem locallyReused (p : Parameters 2 P.dim) (hp : P.family.LocallyReused p) :
    G.LocallyReused (P.embed p) := by
  refine ⟨P.maps_to p hp.1, ?_⟩
  intro U hU
  have hc : ContinuousAt P.embed p := (P.analytic_embed p hp.1).continuousAt
  have hpre : P.embed ⁻¹' U ∈ 𝓝 p := hc.preimage_mem_nhds hU
  apply (hp.2 _ hpre).mono
  rintro z ⟨q, ⟨⟨hq, he⟩, hqU⟩, hqz⟩
  refine ⟨P.embed q, ⟨⟨P.maps_to q hq, ?_⟩, hqU⟩, ?_⟩
  · exact (P.curve_eq q hq).symm.trans (he.trans (P.curve_eq p hp.1))
  · exact (P.keep_center q hq).trans hqz

theorem localReuseNotCovered_mono (h : P.family.LocalReuseNotCovered) :
    G.LocalReuseNotCovered := by
  intro V
  apply (h V).mono
  rintro z ⟨u, hl, hn⟩
  let q := P.embed (z, u)
  have hz : q.1 = z := P.keep_center (z, u) hl.1
  have hlocal := P.locallyReused (z, u) hl
  have hnot : ¬ G.Covered V q := by
    intro hc
    exact hn (P.family.covered_of_curve_eq G P.analytic_family.isSmooth (z, u) hl.1 q V
      (P.curve_eq (z, u) hl.1) hc)
  refine ⟨q.2, ?_, ?_⟩
  · change G.LocallyReused (q.1, q.2) at hlocal
    rwa [hz] at hlocal
  · change ¬ G.Covered V (q.1, q.2) at hnot
    rwa [hz] at hnot

/-- Composition is still centre-preserving; auxiliary dimensions decrease
transitively, and inverse continuity is required only on the actual image. -/
def comp (Q : AnalyticPiece P.family) : AnalyticPiece G where
  dim := Q.dim
  dim_le := Q.dim_le.trans P.dim_le
  family := Q.family
  interval_eq := Q.interval_eq.trans P.interval_eq
  open_domain := Q.open_domain
  bounded_domain := Q.bounded_domain
  connected_domain := Q.connected_domain
  analytic_family := Q.analytic_family
  embed := P.embed ∘ Q.embed
  inverse := Q.inverse ∘ P.inverse
  analytic_embed := fun p hp => (P.analytic_embed _ (Q.maps_to p hp)).comp (Q.analytic_embed p hp)
  continuous_inverse := by
    apply Q.continuous_inverse.comp
    · exact P.continuous_inverse.mono (by
        rintro _ ⟨p, hp, rfl⟩
        exact ⟨Q.embed p, Q.maps_to p hp, rfl⟩)
    · rintro _ ⟨p, hp, rfl⟩
      change P.inverse (P.embed (Q.embed p)) ∈ Q.embed '' Q.family.W
      rw [P.left_inv _ (Q.maps_to p hp)]
      exact mem_image_of_mem _ hp
  left_inv := by
    intro p hp
    simp only [Function.comp_apply, P.left_inv _ (Q.maps_to p hp), Q.left_inv p hp]
  keep_center := by
    intro p hp
    exact (P.keep_center _ (Q.maps_to p hp)).trans (Q.keep_center p hp)
  maps_to := fun p hp => P.maps_to _ (Q.maps_to p hp)
  identity := by
    intro p hp t ht
    exact (Q.identity p hp t (P.interval_eq ▸ ht)).trans (P.identity _ (Q.maps_to p hp) t ht)

end AnalyticPiece

structure RankPiece {d : ℕ} (G : Family 2 d) extends AnalyticPiece G where
  point_rank : ℕ
  curve_rank : ℕ
  ranks : ConstantRanks family point_rank curve_rank
  centers_measurable : ∀ β : Set Plane, MeasurableSet (family.centersOf β)

def RankPiece.comp {d : ℕ} {G : Family 2 d} (P : AnalyticPiece G) (Q : RankPiece P.family) :
    RankPiece G :=
  { P.comp Q.toAnalyticPiece with
    point_rank := Q.point_rank
    curve_rank := Q.curve_rank
    ranks := Q.ranks
    centers_measurable := Q.centers_measurable }

end PlanarNikodym
