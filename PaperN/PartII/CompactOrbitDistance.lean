import PaperN.PartII.CompactSetAction

namespace PaperN.PartII
open Set Metric
variable {G X : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    [MetricSpace X] [MulAction G X] [ContinuousSMul G X] [IsIsometricSMul G X]

/-- Distance between orbits, on representatives. -/
noncomputable def compactOrbitDist (x y : X) : ℝ := infDist x (Set.range fun g : G ↦ g • y)

omit [IsIsometricSMul G X] in
/-- Compactness ensures that the orbit infimum is attained. -/
theorem compactOrbitDist_attained (x y : X) :
    ∃ g : G, compactOrbitDist (G := G) x y = dist x (g • y) := by
  obtain ⟨z, ⟨g, rfl⟩, h⟩ := (isCompact_range (continuous_id.smul continuous_const :
    Continuous (fun g : G ↦ g • y))).exists_infDist_eq_dist (Set.range_nonempty _) x
  exact ⟨g, h⟩

omit [TopologicalSpace G] [CompactSpace G] [ContinuousSMul G X] [IsIsometricSMul G X] in
theorem compactOrbitDist_nonneg (x y : X) : 0 ≤ compactOrbitDist (G := G) x y := infDist_nonneg

omit [TopologicalSpace G] [CompactSpace G] [ContinuousSMul G X] [IsIsometricSMul G X] in
theorem compactOrbitDist_le (x y : X) (g : G) : compactOrbitDist (G := G) x y ≤ dist x (g • y) :=
  infDist_le_dist_of_mem (Set.mem_range_self g)

omit [IsIsometricSMul G X] in
/-- Zero orbit distance means the representatives belong to the same orbit. -/
theorem compactOrbitDist_eq_zero_iff (x y : X) :
    compactOrbitDist (G := G) x y = 0 ↔ ∃ g : G, x = g • y := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := compactOrbitDist_attained (G := G) x y
    exact ⟨g, dist_eq_zero.mp (hg.symm.trans h)⟩
  · rintro ⟨g, rfl⟩
    exact le_antisymm (by simpa using compactOrbitDist_le (g • y) y g) (compactOrbitDist_nonneg _ _)

theorem compactOrbitDist_symm (x y : X) : compactOrbitDist (G := G) x y = compactOrbitDist (G := G) y x := by
  have h (a b : X) : compactOrbitDist (G := G) a b ≤ compactOrbitDist (G := G) b a := by
    obtain ⟨g, hg⟩ := compactOrbitDist_attained (G := G) b a
    rw [hg]
    calc
      _ ≤ dist a (g⁻¹ • b) := compactOrbitDist_le _ _ _
      _ = dist b (g • a) := by
        rw [← (isometry_smul X g).dist_eq a (g⁻¹ • b), smul_inv_smul, dist_comm]
  exact le_antisymm (h x y) (h y x)

theorem compactOrbitDist_triangle (x y z : X) :
    compactOrbitDist (G := G) x z ≤ compactOrbitDist (G := G) x y + compactOrbitDist (G := G) y z := by
  obtain ⟨g, hg⟩ := compactOrbitDist_attained (G := G) x y
  obtain ⟨h, hh⟩ := compactOrbitDist_attained (G := G) y z
  rw [hg, hh]
  calc
    _ ≤ dist x ((g * h) • z) := compactOrbitDist_le _ _ _
    _ ≤ dist x (g • y) + dist (g • y) ((g * h) • z) := dist_triangle _ _ _
    _ = _ := by rw [mul_smul, (isometry_smul X g).dist_eq]

end PaperN.PartII
