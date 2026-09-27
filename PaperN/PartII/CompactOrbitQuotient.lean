import PaperN.PartII.CompactOrbitDistance

namespace PaperN.PartII
variable {G X : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    [MetricSpace X] [MulAction G X] [ContinuousSMul G X] [IsIsometricSMul G X]

/-- Zero orbit distance defines exactly the orbit equivalence relation. -/
def compactOrbitSetoid (G : Type*) {X : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    [MetricSpace X] [MulAction G X] [ContinuousSMul G X] [IsIsometricSMul G X] : Setoid X where
  r x y := compactOrbitDist (G := G) x y = 0
  iseqv := {
    refl := fun x ↦ (compactOrbitDist_eq_zero_iff x x).mpr ⟨1, by simp⟩
    symm := fun h ↦ (compactOrbitDist_symm _ _).trans h
    trans := fun hxy hyz ↦ le_antisymm
      ((compactOrbitDist_triangle _ _ _).trans (by rw [hxy, hyz]; simp))
      (compactOrbitDist_nonneg _ _) }

/-- Orbit distance is independent of both representatives. -/
theorem compactOrbitDist_congr {x x' y y' : X}
    (hx : compactOrbitDist (G := G) x x' = 0) (hy : compactOrbitDist (G := G) y y' = 0) :
    compactOrbitDist (G := G) x y = compactOrbitDist (G := G) x' y' := by
  have hx' : compactOrbitDist (G := G) x' x = 0 := (compactOrbitDist_symm _ _).trans hx
  have hy' : compactOrbitDist (G := G) y' y = 0 := (compactOrbitDist_symm _ _).trans hy
  have h1 := compactOrbitDist_triangle (G := G) x x' y
  have h2 := compactOrbitDist_triangle (G := G) x' y' y
  have h3 := compactOrbitDist_triangle (G := G) x' x y'
  have h4 := compactOrbitDist_triangle (G := G) x y y'
  linarith

/-- The orbit quotient, using the zero-distance characterization of orbits. -/
abbrev CompactOrbitQuotient (G : Type*) (X : Type*) [Group G] [TopologicalSpace G] [CompactSpace G]
    [MetricSpace X] [MulAction G X] [ContinuousSMul G X] [IsIsometricSMul G X] :=
  Quotient (compactOrbitSetoid G (X := X))

noncomputable instance compactOrbitQuotientMetric : MetricSpace (CompactOrbitQuotient G X) where
  dist a b := Quotient.liftOn₂ a b (compactOrbitDist (G := G))
    (fun _ _ _ _ hx hy ↦ compactOrbitDist_congr hx hy)
  dist_self a := Quotient.inductionOn a (fun x ↦ (compactOrbitSetoid G).refl x)
  dist_comm a b := Quotient.inductionOn₂ a b (compactOrbitDist_symm (G := G))
  dist_triangle a b c := Quotient.inductionOn₃ a b c (compactOrbitDist_triangle (G := G))
  eq_of_dist_eq_zero := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro x y h
    exact Quotient.sound h

/-- The quotient metric has the advertised representative formula. -/
theorem compactOrbitQuotient_dist (x y : X) :
    dist (Quotient.mk (compactOrbitSetoid G) x) (Quotient.mk (compactOrbitSetoid G) y) =
      compactOrbitDist (G := G) x y := rfl

/-- Equality in the quotient is precisely equality up to a group element. -/
theorem compactOrbitQuotient_eq_iff (x y : X) :
    Quotient.mk (compactOrbitSetoid G) x = Quotient.mk (compactOrbitSetoid G) y ↔ ∃ g : G, x = g • y := by
  rw [Quotient.eq]
  exact compactOrbitDist_eq_zero_iff x y

/-- Projection to the orbit metric quotient is 1-Lipschitz. -/
theorem compactOrbitQuotient_lipschitz :
    LipschitzWith 1 (Quotient.mk (compactOrbitSetoid G) : X → CompactOrbitQuotient G X) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [compactOrbitQuotient_dist, one_smul, NNReal.coe_one, one_mul] using
    compactOrbitDist_le (G := G) x y 1

end PaperN.PartII
