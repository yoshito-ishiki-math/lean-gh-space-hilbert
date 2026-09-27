import Mathlib.Topology.MetricSpace.GromovHausdorff
import Mathlib.Topology.MetricSpace.Ultra.Basic

namespace PaperN.PartIV
open GromovHausdorff

/-- Ultrametricity transfers along an isometric embedding. -/
theorem ultrametric_of_isometry {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [IsUltrametricDist Y] {f : X → Y} (hf : Isometry f) : IsUltrametricDist X := by
  constructor
  intro x y z
  simpa only [hf.dist_eq] using dist_triangle_max (f x) (f y) (f z)

/-- Ultrametricity is a property of the isometry class. -/
theorem ultrametric_iff_isometryEquiv {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (e : X ≃ᵢ Y) : IsUltrametricDist X ↔ IsUltrametricDist Y := by
  constructor
  · intro h
    letI := h
    exact ultrametric_of_isometry e.symm.isometry
  · intro h
    letI := h
    exact ultrametric_of_isometry e.isometry

/-- Isometry classes of nonempty compact ultrametric spaces.
This definition supplies only the carrier, not the ordinary GH subspace metric. -/
@[ext] structure UltrametricGH where
  val : GHSpace
  property : IsUltrametricDist val.Rep

/-- The property of the chosen GH representative agrees with every concrete carrier. -/
theorem ultrametric_toGHSpace_iff (X : Type*) [MetricSpace X] [CompactSpace X] [Nonempty X] :
    IsUltrametricDist (toGHSpace X).Rep ↔ IsUltrametricDist X := by
  obtain ⟨e⟩ := toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp
    (GHSpace.toGHSpace_rep (toGHSpace X))
  exact ultrametric_iff_isometryEquiv e

noncomputable def toUltrametricGH (X : Type*) [MetricSpace X] [CompactSpace X]
    [Nonempty X] [IsUltrametricDist X] : UltrametricGH :=
  ⟨toGHSpace X, (ultrametric_toGHSpace_iff X).mpr inferInstance⟩

/-- The carrier identifies precisely isometric spaces, including across universes. -/
theorem toUltrametricGH_eq_iff (X Y : Type*) [MetricSpace X] [CompactSpace X]
    [Nonempty X] [IsUltrametricDist X] [MetricSpace Y] [CompactSpace Y]
    [Nonempty Y] [IsUltrametricDist Y] :
    toUltrametricGH X = toUltrametricGH Y ↔ Nonempty (X ≃ᵢ Y) := by
  constructor
  · intro h
    exact toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp (congrArg UltrametricGH.val h)
  · intro h
    apply UltrametricGH.ext
    exact toGHSpace_eq_toGHSpace_iff_isometryEquiv.mpr h

instance (q : UltrametricGH) : IsUltrametricDist q.val.Rep := q.property

/-- Every class is represented by a compact nonempty ultrametric space. -/
theorem toUltrametricGH_rep (q : UltrametricGH) : toUltrametricGH q.val.Rep = q := by
  apply UltrametricGH.ext
  exact GHSpace.toGHSpace_rep q.val

end PaperN.PartIV
