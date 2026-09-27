import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.Topology.MetricSpace.Polish

/-! The Polish-space specialization of Valov, arXiv:0801.1721v2, Theorem 1.1.
Only its continuous-right-inverse consequence is imported, not an invariant selection.
All probabilities on a Polish Borel space are Radon; no compact-support condition is imposed.
No inhabitant of the input is supplied. -/
namespace PaperN.PartI
open MeasureTheory TopologicalSpace

universe u v
variable {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

/-- Pushforward with the weak topologies already used by mathlib. -/
noncomputable def probabilityPushforward (f : C(X, Y)) :
    C(ProbabilityMeasure X, ProbabilityMeasure Y) :=
  ⟨fun μ ↦ μ.map f,
    ProbabilityMeasure.continuous_map f.continuous⟩

/-- A cited consequence of softness for an open continuous surjection.
Polish is a deliberate specialization, not a formalization of Valov's full nonseparable theorem. -/
structure ValovProbabilityInput [PolishSpace X] [PolishSpace Y] (f : C(X, Y)) : Prop where
  rightInverse : IsOpenMap f → Function.Surjective f →
    ∃ R : C(ProbabilityMeasure Y, ProbabilityMeasure X),
      Function.RightInverse R (probabilityPushforward f)

end PaperN.PartI
