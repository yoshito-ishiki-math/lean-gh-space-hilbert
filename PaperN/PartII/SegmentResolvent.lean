import PaperN.PartII.ResolventIntegrability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace PaperN.PartII
open MeasureTheory Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

def segmentParameter (a b : ℂ) (t : ℝ) : ℂ := a + (t : ℂ) * (b-a)

noncomputable def segmentResolvent (U : E →L[ℂ] E) (a b : ℂ) : E →L[ℂ] E :=
  ∫ t in (0 : ℝ)..1, (b-a) • resolvent U (segmentParameter a b t)

theorem segmentResolvent_integrable (U : E →L[ℂ] E) (a b : ℂ)
    (hz : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter a b t ∈ resolventSet ℂ U) :
    IntervalIntegrable (fun t ↦ (b-a) • resolvent U (segmentParameter a b t)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  intro t ht
  have hc : ContinuousAt (fun s : ℝ ↦ segmentParameter a b s) t := by
    unfold segmentParameter
    fun_prop
  have hd : ContinuousAt (fun _ : ℝ ↦ b-a) t := continuousAt_const
  exact (hd.smul
    ((spectrum.hasDerivAt_resolvent_const_left (hz t ht)).continuousAt.comp hc)).continuousWithinAt

theorem segmentResolvent_intertwine (U : E →L[ℂ] E) (T : F →L[ℂ] F)
    (R : E →L[ℂ] F) (h : ∀ x, R (U x) = T (R x)) (a b : ℂ)
    (hU : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter a b t ∈ resolventSet ℂ U)
    (hT : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter a b t ∈ resolventSet ℂ T) :
    R.comp (segmentResolvent U a b) = (segmentResolvent T a b).comp R := by
  let L := ContinuousLinearMap.compL ℂ E E F R
  let M := (ContinuousLinearMap.compL ℂ E F F).flip R
  have hu := segmentResolvent_integrable U a b hU
  have ht := segmentResolvent_integrable T a b hT
  change L (∫ t in (0 : ℝ)..1, (b-a) • resolvent U (segmentParameter a b t)) =
    M (∫ t in (0 : ℝ)..1, (b-a) • resolvent T (segmentParameter a b t))
  rw [← L.intervalIntegral_comp_comm hu, ← M.intervalIntegral_comp_comm ht]
  apply intervalIntegral.integral_congr
  intro t hmem
  have hh : t ∈ Icc (0 : ℝ) 1 := by simpa using hmem
  apply ContinuousLinearMap.ext
  intro x
  change R ((b-a) • resolvent U (segmentParameter a b t) x) =
    (b-a) • resolvent T (segmentParameter a b t) (R x)
  rw [map_smul, resolvent_intertwine U T R h _ (hU t hh) (hT t hh)]
/-- Four oriented edges with the Cauchy normalization; projection properties are separate. -/
noncomputable def quadrilateralResolvent (U : E →L[ℂ] E) (a b c d : ℂ) : E →L[ℂ] E :=
  (2 * Real.pi * Complex.I)⁻¹ •
    (segmentResolvent U a b + segmentResolvent U b c +
      segmentResolvent U c d + segmentResolvent U d a)

theorem quadrilateralResolvent_intertwine (U : E →L[ℂ] E) (T : F →L[ℂ] F)
    (R : E →L[ℂ] F) (h : ∀ x, R (U x) = T (R x)) (a b c d : ℂ)
    (hab : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter a b t ∈ resolventSet ℂ U ∩ resolventSet ℂ T)
    (hbc : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter b c t ∈ resolventSet ℂ U ∩ resolventSet ℂ T)
    (hcd : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter c d t ∈ resolventSet ℂ U ∩ resolventSet ℂ T)
    (hda : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter d a t ∈ resolventSet ℂ U ∩ resolventSet ℂ T) :
    R.comp (quadrilateralResolvent U a b c d) =
      (quadrilateralResolvent T a b c d).comp R := by
  have H (p q : ℂ) (hpq : ∀ t ∈ Icc (0 : ℝ) 1,
      segmentParameter p q t ∈ resolventSet ℂ U ∩ resolventSet ℂ T) (x : E) :
      R (segmentResolvent U p q x) = segmentResolvent T p q (R x) :=
    congrArg (fun A : E →L[ℂ] F ↦ A x)
      (segmentResolvent_intertwine U T R h p q (fun t ht ↦ (hpq t ht).1)
        (fun t ht ↦ (hpq t ht).2))
  apply ContinuousLinearMap.ext
  intro x
  change R ((2 * Real.pi * Complex.I)⁻¹ •
    (segmentResolvent U a b x + segmentResolvent U b c x +
      segmentResolvent U c d x + segmentResolvent U d a x)) =
    (2 * Real.pi * Complex.I)⁻¹ •
    (segmentResolvent T a b (R x) + segmentResolvent T b c (R x) +
      segmentResolvent T c d (R x) + segmentResolvent T d a (R x))
  rw [map_smul, map_add, map_add, map_add, H a b hab, H b c hbc, H c d hcd, H d a hda]
end PaperN.PartII
