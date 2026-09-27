import PaperN.PartI.GHPDistance

/-! Explicit external inputs specialized from Khezeli, arXiv:1812.03760v5.
No inhabitant of either input is supplied here. See EXTERNAL-INPUTS.md. -/
namespace PaperN.PartI
open TopologicalSpace
universe u

/-- Named constructor preserving the measured quotient type during instance inference. -/
def MeasuredCompact.toMeasuredGHSpace (X : MeasuredCompact.{u}) : MeasuredGHSpace.{u} :=
  Quotient.mk _ X

/-- The missing metric properties from Theorem 2.6, specialized using Example 2.1(iii)
and Lemma 2.8. Known nonnegativity, symmetry and the diagonal law are not re-assumed. -/
structure GHPMetricInput : Prop where
  triangle : ∀ x y z : MeasuredGHSpace.{u},
    MeasuredGHSpace.distance x z ≤ MeasuredGHSpace.distance x y + MeasuredGHSpace.distance y z
  separated : ∀ x y : MeasuredGHSpace.{u}, MeasuredGHSpace.distance x y = 0 → x = y

/-- Build the metric from the exact max-infimum and the two explicit cited properties.
This is not a global instance and does not construct a value of GHPMetricInput. -/
noncomputable abbrev GHPMetricInput.metricSpace (h : GHPMetricInput.{u}) :
    MetricSpace MeasuredGHSpace.{u} where
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
  dist_triangle := h.triangle
  eq_of_dist_eq_zero := h.separated _ _

/-- Theorem 2.12 specialized to probabilities, using Lemmas 2.8 and 2.13.
Both properties refer to the above exact GHP metric, not an arbitrary Polish topology. -/
structure GHPPolishInput (h : GHPMetricInput.{u}) : Prop where
  complete : @CompleteSpace MeasuredGHSpace.{u} h.metricSpace.toUniformSpace
  separable : @SeparableSpace MeasuredGHSpace.{u} h.metricSpace.toUniformSpace.toTopologicalSpace

end PaperN.PartI
