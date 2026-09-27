import PaperN.PartI.Definitions
import Mathlib.Topology.ContinuousMap.Compact

namespace PaperN.PartI
open MeasureTheory Filter TopologicalSpace
open scoped Topology
variable (Z P 𝕜 : Type*) [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [CompactSpace Z] [MetricSpace P] [CompactSpace P] [RCLike 𝕜]

/-- `lem:uniform-weak-integrals`: the exact supremum error, for ℝ or ℂ. -/
def UniformWeakIntegralsStatement : Prop :=
  ∀ (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z),
    Tendsto μs atTop (𝓝 μ) → ∀ K : Set C(Z, 𝕜), IsCompact K → K.Nonempty →
      Tendsto (fun n ↦ ⨆ f : K,
        ‖(∫ z, f.val z ∂(μs n : Measure Z)) - ∫ z, f.val z ∂(μ : Measure Z)‖)
        atTop (𝓝 0)

/-- `lem:parameter-integrals`: both the measure and the continuous integrand vary. -/
def ParameterIntegralsStatement : Prop :=
  ∀ (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z),
    Tendsto μs atTop (𝓝 μ) → ∀ (Fs : ℕ → C(P × Z, 𝕜)) (F : C(P × Z, 𝕜)),
      Tendsto (fun n ↦ ‖Fs n - F‖) atTop (𝓝 0) →
      Tendsto (fun n ↦ ⨆ p : P,
        ‖(∫ z, Fs n (p, z) ∂(μs n : Measure Z)) - ∫ z, F (p, z) ∂(μ : Measure Z)‖)
        atTop (𝓝 0)
end PaperN.PartI
