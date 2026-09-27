import PaperN.PartII.IntegratedResolvent
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace PaperN.PartII
open MeasureTheory
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
variable [MeasurableSpace Ω] [BorelSpace Ω]

omit [CompactSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] in
theorem continuous_weighted_resolvent (U : E →L[ℂ] E) (z w : C(Ω, ℂ))
    (hz : ∀ t, z t ∈ resolventSet ℂ U) :
    Continuous (fun t ↦ w t • resolvent U (z t)) := by
  have hr : ContinuousOn (resolvent U) (resolventSet ℂ U) :=
    HasDerivAt.continuousOn (fun _ h ↦ spectrum.hasDerivAt_resolvent_const_left h)
  exact w.continuous.smul (hr.comp_continuous z.continuous hz)

theorem integrable_weighted_resolvent (U : E →L[ℂ] E) (ν : Measure Ω) [IsFiniteMeasure ν]
    (z w : C(Ω, ℂ)) (hz : ∀ t, z t ∈ resolventSet ℂ U) :
    Integrable (fun t ↦ w t • resolvent U (z t)) ν :=
  (continuous_weighted_resolvent U z w hz).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem compact_integratedResolvent_intertwine (U : E →L[ℂ] E) (T : F →L[ℂ] F)
    (R : E →L[ℂ] F) (h : ∀ x, R (U x) = T (R x))
    (ν : Measure Ω) [IsFiniteMeasure ν] (z w : C(Ω, ℂ))
    (hU : ∀ t, z t ∈ resolventSet ℂ U) (hT : ∀ t, z t ∈ resolventSet ℂ T) :
    R.comp (integratedResolvent U ν z w) = (integratedResolvent T ν z w).comp R :=
  integratedResolvent_intertwine U T R h ν z w hU hT
    (integrable_weighted_resolvent U ν z w hU) (integrable_weighted_resolvent T ν z w hT)

namespace AmbientKernel
universe u v
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Z : Type v} [MetricSpace Z] [CompactSpace Z]
variable (e : C(X, Z)) (μ : Measure X) [IsProbabilityMeasure μ]

theorem restriction_compact_integratedResolvent (he : Isometry e)
    (ν : Measure Ω) [IsFiniteMeasure ν] (z w : C(Ω, ℂ))
    (hz : ∀ t, z t ≠ 0)
    (hT : ∀ t, z t ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ)) :
    (restriction e μ).comp (integratedResolvent (ambientOperator e μ) ν z w) =
      (integratedResolvent (ComplexKernel.distanceOperator μ) ν z w).comp (restriction e μ) :=
  compact_integratedResolvent_intertwine _ _ _ (restriction_intertwine e μ he) ν z w
    (fun t ↦ (nonzero_resolventSet_iff e μ he (z t) (hz t)).mpr (hT t)) hT
end AmbientKernel
end PaperN.PartII
