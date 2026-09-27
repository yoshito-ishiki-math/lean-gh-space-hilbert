import PaperN.PartII.CompactOrbitQuotient

namespace PaperN.PartII
open Set Metric
variable {G X : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    [MetricSpace X] [MulAction G X] [ContinuousSMul G X] [IsIsometricSMul G X]

noncomputable local instance : TopologicalSpace (CompactOrbitQuotient G X) :=
  (compactOrbitQuotientMetric (G := G) (X := X)).toUniformSpace.toTopologicalSpace

/-- Orbit projection maps each open ball onto the corresponding quotient ball. -/
theorem compactOrbitQuotient_image_ball (x : X) (r : ℝ) :
    Quotient.mk (compactOrbitSetoid G) '' ball x r =
      ball (Quotient.mk (compactOrbitSetoid G) x) r := by
  ext q
  refine Quotient.inductionOn q ?_
  intro y
  constructor
  · rintro ⟨z, hz, he⟩
    rw [← he]
    have hle : dist (Quotient.mk (compactOrbitSetoid G) z)
        (Quotient.mk (compactOrbitSetoid G) x) ≤ dist z x := by
      simpa only [compactOrbitQuotient_dist, one_smul] using
        (compactOrbitDist_le (G := G) z x 1)
    exact hle.trans_lt hz
  · intro hy
    have hxy : compactOrbitDist (G := G) x y < r := by
      simpa only [mem_ball, compactOrbitQuotient_dist, compactOrbitDist_symm y x] using hy
    obtain ⟨g, hg⟩ := compactOrbitDist_attained (G := G) x y
    refine ⟨g • y, ?_, ?_⟩
    · simpa only [mem_ball, dist_comm, ← hg] using hxy
    · exact (compactOrbitQuotient_eq_iff (g • y) y).mpr ⟨g, rfl⟩

/-- The orbit metric projection is open. -/
theorem compactOrbitQuotient_isOpenMap :
    IsOpenMap (Quotient.mk (compactOrbitSetoid G) : X → CompactOrbitQuotient G X) := by
  intro U hU
  rw [Metric.isOpen_iff]
  rintro q ⟨x, hx, rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  refine ⟨r, hr, ?_⟩
  rw [← compactOrbitQuotient_image_ball]
  exact Set.image_mono hball

/-- The metric topology is exactly the quotient topology of the orbit projection. -/
theorem compactOrbitQuotient_isQuotientMap :
    Topology.IsQuotientMap (Quotient.mk (compactOrbitSetoid G) : X → CompactOrbitQuotient G X) :=
  compactOrbitQuotient_isOpenMap.isQuotientMap compactOrbitQuotient_lipschitz.continuous
    (fun q ↦ Quotient.exists_rep q)

/-- Explicit equality of the constructed metric topology and the coinduced topology. -/
theorem compactOrbitQuotient_topology_eq :
    (compactOrbitQuotientMetric (G := G) (X := X)).toUniformSpace.toTopologicalSpace =
      TopologicalSpace.coinduced (Quotient.mk (compactOrbitSetoid G))
        (inferInstance : TopologicalSpace X) :=
  compactOrbitQuotient_isQuotientMap.isCoinducing.eq_coinduced

end PaperN.PartII
