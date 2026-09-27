import PaperN.PartII.ResolventIntertwining

namespace PaperN.PartII
open MeasureTheory
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Weighted operator integral; a projection property is not part of this definition. -/
noncomputable def integratedResolvent (U : E →L[ℂ] E) (ν : Measure Ω)
    (z w : Ω → ℂ) : E →L[ℂ] E := ∫ t, w t • resolvent U (z t) ∂ν

omit [CompleteSpace E] in
theorem integratedResolvent_apply (U : E →L[ℂ] E) (ν : Measure Ω) (z w : Ω → ℂ)
    (hi : Integrable (fun t ↦ w t • resolvent U (z t)) ν) (x : E) :
    integratedResolvent U ν z w x = ∫ t, w t • resolvent U (z t) x ∂ν :=
  ContinuousLinearMap.integral_apply hi x

theorem integratedResolvent_intertwine (U : E →L[ℂ] E) (T : F →L[ℂ] F)
    (R : E →L[ℂ] F) (h : ∀ x, R (U x) = T (R x))
    (ν : Measure Ω) (z w : Ω → ℂ)
    (hU : ∀ t, z t ∈ resolventSet ℂ U) (hT : ∀ t, z t ∈ resolventSet ℂ T)
    (hiU : Integrable (fun t ↦ w t • resolvent U (z t)) ν)
    (hiT : Integrable (fun t ↦ w t • resolvent T (z t)) ν) :
    R.comp (integratedResolvent U ν z w) = (integratedResolvent T ν z w).comp R := by
  apply ContinuousLinearMap.ext
  intro x
  change R (integratedResolvent U ν z w x) = integratedResolvent T ν z w (R x)
  rw [integratedResolvent_apply U ν z w hiU, integratedResolvent_apply T ν z w hiT]
  apply integral_resolvent_intertwine U T R h ν z w hU hT x
  exact (ContinuousLinearMap.apply ℂ E x).integrable_comp hiU

/-- Intertwining carries the image of one integrated operator into the other image. -/
theorem integratedResolvent_range_map_le (U : E →L[ℂ] E) (T : F →L[ℂ] F)
    (R : E →L[ℂ] F) (h : ∀ x, R (U x) = T (R x))
    (ν : Measure Ω) (z w : Ω → ℂ)
    (hU : ∀ t, z t ∈ resolventSet ℂ U) (hT : ∀ t, z t ∈ resolventSet ℂ T)
    (hiU : Integrable (fun t ↦ w t • resolvent U (z t)) ν)
    (hiT : Integrable (fun t ↦ w t • resolvent T (z t)) ν) :
    Submodule.map R.toLinearMap (LinearMap.range (integratedResolvent U ν z w).toLinearMap) ≤
      LinearMap.range (integratedResolvent T ν z w).toLinearMap := by
  rintro y ⟨v, ⟨x, rfl⟩, rfl⟩
  refine ⟨R x, ?_⟩
  exact (congrArg (fun A : E →L[ℂ] F ↦ A x)
    (integratedResolvent_intertwine U T R h ν z w hU hT hiU hiT)).symm
namespace AmbientKernel
universe u v
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Z : Type v} [MetricSpace Z] [CompactSpace Z]
variable (e : C(X, Z)) (μ : Measure X) [IsProbabilityMeasure μ]

theorem restriction_integratedResolvent (he : Isometry e) (ν : Measure Ω) (z w : Ω → ℂ)
    (hz : ∀ t, z t ≠ 0)
    (hT : ∀ t, z t ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (hiU : Integrable (fun t ↦ w t • resolvent (ambientOperator e μ) (z t)) ν)
    (hiT : Integrable (fun t ↦ w t • resolvent (ComplexKernel.distanceOperator μ) (z t)) ν) :
    (restriction e μ).comp (integratedResolvent (ambientOperator e μ) ν z w) =
      (integratedResolvent (ComplexKernel.distanceOperator μ) ν z w).comp (restriction e μ) :=
  integratedResolvent_intertwine _ _ _ (restriction_intertwine e μ he) ν z w
    (fun t ↦ (nonzero_resolventSet_iff e μ he (z t) (hz t)).mpr (hT t)) hT hiU hiT
end AmbientKernel
end PaperN.PartII
