import PaperN.PartI.ValovInput
import Mathlib.MeasureTheory.Measure.Support

namespace PaperN.PartI
open MeasureTheory TopologicalSpace
universe u v
variable {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

/-- The Polish specialization of manuscript `thm:valov`. -/
def ValovSelectionStatement (f : C(X, Y)) : Prop :=
  ∃ s : C(Y, ProbabilityMeasure X),
    ∀ y, probabilityPushforward f (s y) = diracProba y

/-- The selected probabilities give full mass to their fibers, and their support is in the fiber.
This does not assert full support on the fiber or invariance under a group. -/
def FiberLawSelectionStatement (f : C(X, Y)) : Prop :=
  ∃ s : C(Y, ProbabilityMeasure X), ∀ y,
    probabilityPushforward f (s y) = diracProba y ∧
    (s y : Measure X) (f ⁻¹' {y}) = 1 ∧
    (s y : Measure X).support ⊆ f ⁻¹' {y}

end PaperN.PartI
