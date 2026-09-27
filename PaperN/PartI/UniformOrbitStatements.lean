import PaperN.PartI.CommonIsometryLimits

namespace PaperN.PartI
open MeasureTheory Set Filter TopologicalSpace
open scoped Topology BoundedContinuousFunction
universe u
namespace CommonRealization
variable {Xs : ℕ → MeasuredCompact.{u}} {X : MeasuredCompact.{u}}

noncomputable def orbitProbabilityAt (C : CommonRealization Xs X) (n : ℕ)
    (g : Xs n ≃ᵢ Xs n) : ProbabilityMeasure C :=
  (Xs n).probability.map ((C.seq_isometry n).continuous.comp g.continuous).measurable.aemeasurable

noncomputable def orbitError (C : CommonRealization Xs X) (f : C →ᵇ ℝ) (n : ℕ)
    (g : Xs n ≃ᵢ Xs n) : ℝ :=
  ‖(∫ z, f z ∂(C.orbitProbabilityAt n g : Measure C)) -
    ∫ z, f z ∂(C.limitProbability : Measure C)‖

/-- The uniform orbit-integral conclusion used inside `lem:convergent-invariant-lifts`. -/
def UniformOrbitIntegralsStatement (C : CommonRealization Xs X) : Prop :=
  C.HausdorffConverges → C.WeakConverges →
    (∀ g : X ≃ᵢ X, Measure.map g X.measure = X.measure) →
    ∀ f : C →ᵇ ℝ, Tendsto (fun n ↦ ⨆ g : Xs n ≃ᵢ Xs n, C.orbitError f n g) atTop (𝓝 0)
end CommonRealization
end PaperN.PartI
