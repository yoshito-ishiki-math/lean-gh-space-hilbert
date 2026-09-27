import PaperN.PartI.CompactCouplingGluing
import PaperN.PartI.GHPMetricInput

namespace PaperN.PartI
universe u

/-- The remaining metric axiom: zero GHP distance identifies measured isometry classes. -/
def GHPSeparationStatement : Prop :=
  ∀ x y : MeasuredGHSpace.{u}, MeasuredGHSpace.distance x y = 0 → x = y

/-- Triangle inequality is supplied internally, so separation alone constructs
all fields of the previously exposed metric input. -/
theorem ghpMetricInput_of_separation (hs : GHPSeparationStatement.{u}) : GHPMetricInput.{u} :=
  ⟨MeasuredGHSpace.distance_triangle, hs⟩

/-- The old metric-input package is equivalent to its remaining separation field. -/
theorem ghpMetricInput_iff_separation : GHPMetricInput.{u} ↔ GHPSeparationStatement.{u} :=
  ⟨fun h ↦ h.separated, ghpMetricInput_of_separation⟩

/-- The constructed metric still uses the manuscript's exact max-infimum distance. -/
theorem ghpMetricInput_of_separation_dist (hs : GHPSeparationStatement.{u})
    (x y : MeasuredGHSpace.{u}) :
    @dist _ (ghpMetricInput_of_separation hs).metricSpace.toDist x y = MeasuredGHSpace.distance x y := rfl

/-- The max-infimum GHP distance already defines a pseudometric without any external input. -/
noncomputable abbrev MeasuredGHSpace.pseudoMetricSpace : PseudoMetricSpace MeasuredGHSpace.{u} where
  dist := MeasuredGHSpace.distance
  dist_self x := by
    refine Quotient.inductionOn x ?_
    intro X
    change (ghpEDist X X).toReal = 0
    rw [ghpEDist_self]
    rfl
  dist_comm x y := by
    refine Quotient.inductionOn₂ x y ?_
    intro X Y
    change (ghpEDist X Y).toReal = (ghpEDist Y X).toReal
    rw [ghpEDist_comm]
  dist_triangle := MeasuredGHSpace.distance_triangle

/-- Every metric input induces exactly the internally constructed pseudometric. -/
theorem GHPMetricInput.toPseudoMetricSpace_eq (h : GHPMetricInput.{u}) :
    h.metricSpace.toPseudoMetricSpace = MeasuredGHSpace.pseudoMetricSpace := rfl
end PaperN.PartI
