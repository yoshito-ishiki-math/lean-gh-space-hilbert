import PaperN.Shared.Scaling

namespace PaperN.PartIV
open PaperN.Shared GromovHausdorff
universe u v w z

/-- Product of correspondences, with coordinates paired factor by factor. -/
def productCorrespondence {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    (R : Correspondence X X') (S : Correspondence Y Y') : Correspondence (X × Y) (X' × Y') where
  rel := {p | (p.1.1, p.2.1) ∈ R.rel ∧ (p.1.2, p.2.2) ∈ S.rel}
  left_total p := by
    obtain ⟨x, hx⟩ := R.left_total p.1
    obtain ⟨y, hy⟩ := S.left_total p.2
    exact ⟨(x,y), hx, hy⟩
  right_total p := by
    obtain ⟨x, hx⟩ := R.right_total p.1
    obtain ⟨y, hy⟩ := S.right_total p.2
    exact ⟨(x,y), hx, hy⟩

/-- Max-product distortion is bounded by the larger factor distortion. -/
theorem productCorrespondence_distortionLE
    {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace X'] [PseudoMetricSpace Y']
    (R : Correspondence X X') (S : Correspondence Y Y') (a b : ℝ)
    (hR : R.DistortionLE a) (hS : S.DistortionLE b) :
    (productCorrespondence R S).DistortionLE (max a b) := by
  intro p q
  change |max (dist p.val.1.1 q.val.1.1) (dist p.val.1.2 q.val.1.2) -
    max (dist p.val.2.1 q.val.2.1) (dist p.val.2.2 q.val.2.2)| ≤ _
  exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le_max
    (hR ⟨_, p.property.1⟩ ⟨_, q.property.1⟩)
    (hS ⟨_, p.property.2⟩ ⟨_, q.property.2⟩))

/-- The sharp max-product GH bound for arbitrary nonempty compact metric factors. -/
theorem ghDist_prod_le (X : Type u) (Y : Type v) (X' : Type w) (Y' : Type z)
    [MetricSpace X] [MetricSpace Y] [MetricSpace X'] [MetricSpace Y']
    [CompactSpace X] [CompactSpace Y] [CompactSpace X'] [CompactSpace Y']
    [Nonempty X] [Nonempty Y] [Nonempty X'] [Nonempty Y'] :
    ghDist (X × Y) (X' × Y') ≤ max (ghDist X X') (ghDist Y Y') := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  obtain ⟨R, hR⟩ := exists_correspondence_distortion X X' (ghDist X X' + δ) (by linarith)
  obtain ⟨S, hS⟩ := exists_correspondence_distortion Y Y' (ghDist Y Y' + δ) (by linarith)
  have h := ghDist_le_half_distortion (productCorrespondence R S) _
    (productCorrespondence_distortionLE R S _ _ hR hS)
  apply h.trans
  apply (div_le_iff₀ (by norm_num : (0:ℝ) < 2)).mpr
  apply max_le
  · linarith [le_max_left (ghDist X X') (ghDist Y Y')]
  · linarith [le_max_right (ghDist X X') (ghDist Y Y')]

/-- Product on GH classes using the standard max metric. -/
noncomputable def productGH (q r : GHSpace) : GHSpace := toGHSpace (q.Rep × r.Rep)

/-- Joint max-metric control of product on GH classes. -/
theorem productGH_dist_le (q r q' r' : GHSpace) :
    dist (productGH q r) (productGH q' r') ≤ max (dist q q') (dist r r') := by
  simpa only [productGH, ghDist, GHSpace.toGHSpace_rep] using
    ghDist_prod_le q.Rep r.Rep q'.Rep r'.Rep

/-- Product is jointly 1-Lipschitz, hence continuous. -/
theorem productGH_lipschitz :
    LipschitzWith 1 (fun p : GHSpace × GHSpace ↦ productGH p.1 p.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simpa only [NNReal.coe_one, one_mul, Prod.dist_eq] using productGH_dist_le p.1 p.2 q.1 q.2

/-- The representative construction agrees with every concrete product carrier. -/
theorem productGH_toGHSpace (X : Type u) (Y : Type v)
    [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
    [Nonempty X] [Nonempty Y] :
    productGH (toGHSpace X) (toGHSpace Y) = toGHSpace (X × Y) := by
  apply dist_le_zero.mp
  have h := ghDist_prod_le (toGHSpace X).Rep (toGHSpace Y).Rep X Y
  simpa only [productGH, ghDist, GHSpace.toGHSpace_rep, dist_self, max_self] using h

end PaperN.PartIV
