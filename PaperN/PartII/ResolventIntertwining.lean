import PaperN.PartII.AmbientEigenspaces

namespace PaperN.PartII
section General
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F]
variable (U : E →L[ℂ] E) (T : F →L[ℂ] F) (R : E →L[ℂ] F)

theorem inverse_intertwine (h : ∀ x, R (U x) = T (R x))
    (V : E →L[ℂ] E) (S : F →L[ℂ] F)
    (hV : ∀ x, U (V x) = x) (hS : ∀ y, S (T y) = y) (x : E) :
    R (V x) = S (R x) := by
  rw [← hS (R (V x)), ← h, hV]

theorem resolvent_intertwine (h : ∀ x, R (U x) = T (R x)) (z : ℂ)
    (hU : z ∈ resolventSet ℂ U) (hT : z ∈ resolventSet ℂ T) (x : E) :
    R (resolvent U z x) = resolvent T z (R x) := by
  apply inverse_intertwine
    (algebraMap ℂ (E →L[ℂ] E) z - U)
    (algebraMap ℂ (F →L[ℂ] F) z - T) R
  · intro y
    simpa [Algebra.algebraMap_eq_smul_one, map_sub, map_smul] using
      congrArg (fun w ↦ z • R y - w) (h y)
  · intro y
    have hu := Ring.mul_inverse_cancel (algebraMap ℂ (E →L[ℂ] E) z - U) hU
    exact congrArg (fun A : E →L[ℂ] E ↦ A y) hu
  · intro y
    have ht := Ring.inverse_mul_cancel (algebraMap ℂ (F →L[ℂ] F) z - T) hT
    exact congrArg (fun A : F →L[ℂ] F ↦ A y) ht
end General

section Integral
open MeasureTheory
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
variable {Ω : Type*} [MeasurableSpace Ω]

theorem integral_resolvent_intertwine (U : E →L[ℂ] E) (T : F →L[ℂ] F)
    (R : E →L[ℂ] F) (h : ∀ x, R (U x) = T (R x))
    (ν : Measure Ω) (z w : Ω → ℂ)
    (hU : ∀ t, z t ∈ resolventSet ℂ U) (hT : ∀ t, z t ∈ resolventSet ℂ T)
    (x : E) (hi : Integrable (fun t ↦ w t • resolvent U (z t) x) ν) :
    R (∫ t, w t • resolvent U (z t) x ∂ν) =
      ∫ t, w t • resolvent T (z t) (R x) ∂ν := by
  calc
    R (∫ t, w t • resolvent U (z t) x ∂ν) =
        ∫ t, R (w t • resolvent U (z t) x) ∂ν :=
      ((R.restrictScalars ℝ).integral_comp_comm hi).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [map_smul, resolvent_intertwine U T R h (z t) (hU t) (hT t) x]
end Integral

namespace AmbientKernel
open MeasureTheory
universe u v
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Z : Type v} [MetricSpace Z] [CompactSpace Z]
variable (e : C(X, Z)) (μ : Measure X) [IsProbabilityMeasure μ]

theorem restriction_resolvent (he : Isometry e) (z : ℂ)
    (hU : z ∈ resolventSet ℂ (ambientOperator e μ))
    (hT : z ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ)) (f : C(Z, ℂ)) :
    restriction e μ (resolvent (ambientOperator e μ) z f) =
      resolvent (ComplexKernel.distanceOperator μ) z (restriction e μ f) :=
  resolvent_intertwine _ _ _ (restriction_intertwine e μ he) z hU hT f
theorem nonzero_resolventSet_iff (he : Isometry e) (z : ℂ) (hz : z ≠ 0) :
    z ∈ resolventSet ℂ (ambientOperator e μ) ↔
      z ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ) := by
  have hh := Set.ext_iff.mp (ambient_nonzero_spectrum_eq e μ he) z
  simp only [Set.mem_sdiff, Set.mem_singleton_iff, hz, not_false_eq_true, and_true] at hh
  exact not_iff_not.mp hh

theorem restriction_resolvent_of_nonzero (he : Isometry e) (z : ℂ) (hz : z ≠ 0)
    (hT : z ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ)) (f : C(Z, ℂ)) :
    restriction e μ (resolvent (ambientOperator e μ) z f) =
      resolvent (ComplexKernel.distanceOperator μ) z (restriction e μ f) :=
  restriction_resolvent e μ he z ((nonzero_resolventSet_iff e μ he z hz).mpr hT) hT f
end AmbientKernel
end PaperN.PartII
