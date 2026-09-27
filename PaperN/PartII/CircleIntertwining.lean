import PaperN.PartII.TwoCircleProjection

namespace PaperN.PartII
open MeasureTheory Metric Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem circleResolvent_intertwine (U : E →L[ℂ] E) (T : F →L[ℂ] F)
    (R : E →L[ℂ] F) (h : ∀ x, R (U x) = T (R x)) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hU : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ U)
    (hT : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ T) :
    R.comp (circleResolvent U c r) = (circleResolvent T c r).comp R := by
  let L := ContinuousLinearMap.compL ℂ E E F R
  let M := (ContinuousLinearMap.compL ℂ E F F).flip R
  have hu := (circleIntegrable_iff r).mp (circleResolvent_integrable U c r hr hU)
  have ht := (circleIntegrable_iff r).mp (circleResolvent_integrable T c r hr hT)
  change L ((2 * Real.pi * Complex.I)⁻¹ • circleIntegral (resolvent U) c r) =
    M ((2 * Real.pi * Complex.I)⁻¹ • circleIntegral (resolvent T) c r)
  rw [map_smul, map_smul]
  congr 1
  unfold circleIntegral
  rw [← L.intervalIntegral_comp_comm hu, ← M.intervalIntegral_comp_comm ht]
  apply intervalIntegral.integral_congr
  intro t _
  have hz : circleMap c r t ∈ sphere c r := circleMap_mem_sphere c hr t
  apply ContinuousLinearMap.ext
  intro x
  change R ((deriv (circleMap c r) t) • resolvent U (circleMap c r t) x) =
    (deriv (circleMap c r) t) • resolvent T (circleMap c r t) (R x)
  rw [map_smul, resolvent_intertwine U T R h _ (hU _ hz) (hT _ hz)]

theorem twoCircleResolvent_intertwine (U : E →L[ℂ] E) (T : F →L[ℂ] F)
    (R : E →L[ℂ] F) (h : ∀ x, R (U x) = T (R x))
    (c d : ℂ) (r t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hc : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ U ∩ resolventSet ℂ T)
    (hd : ∀ z ∈ sphere d t, z ∈ resolventSet ℂ U ∩ resolventSet ℂ T) :
    R.comp (twoCircleResolvent U c d r t) = (twoCircleResolvent T c d r t).comp R := by
  have h₁ := circleResolvent_intertwine U T R h c r hr
    (fun z hz ↦ (hc z hz).1) (fun z hz ↦ (hc z hz).2)
  have h₂ := circleResolvent_intertwine U T R h d t ht
    (fun z hz ↦ (hd z hz).1) (fun z hz ↦ (hd z hz).2)
  apply ContinuousLinearMap.ext
  intro x
  change R (circleResolvent U c r x + circleResolvent U d t x) =
    circleResolvent T c r (R x) + circleResolvent T d t (R x)
  rw [map_add]
  exact congrArg₂ (fun a b : F ↦ a + b) (DFunLike.congr_fun h₁ x) (DFunLike.congr_fun h₂ x)

omit [CompleteSpace E] in
theorem cutoffCircle_spheres_resolvent (U : E →L[ℂ] E) (η B : ℝ)
    (hB : 0 < B) (hb : ∀ z ∈ spectrum ℂ U, z.im = 0 ∧ ‖z‖ < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ U) (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ U) :
    (∀ z ∈ sphere (((η+B)/2 : ℝ) : ℂ) ((B-η)/2), z ∈ resolventSet ℂ U) ∧
    (∀ z ∈ sphere (((-B + -η)/2 : ℝ) : ℂ) ((-η - -B)/2), z ∈ resolventSet ℂ U) := by
  have hpos : (B : ℂ) ∈ resolventSet ℂ U := by
    by_contra h
    have hh := (hb _ h).2
    simp [Complex.norm_real, abs_of_pos hB] at hh
  have hneg : ((-B : ℝ) : ℂ) ∈ resolventSet ℂ U := by
    by_contra h
    have hh := (hb _ h).2
    simp [Complex.norm_real, abs_of_pos hB] at hh
  exact ⟨circle_real_interval_resolvent U (fun z hz ↦ (hb z hz).1) η B hp hpos,
    circle_real_interval_resolvent U (fun z hz ↦ (hb z hz).1) (-B) (-η) hneg hn⟩

theorem cutoffCircle_intertwine (U : E →L[ℂ] E) (T : F →L[ℂ] F)
    (R : E →L[ℂ] F) (h : ∀ x, R (U x) = T (R x)) (η B : ℝ)
    (hη : 0 < η) (hB : η < B)
    (hU : ∀ z ∈ spectrum ℂ U, z.im = 0 ∧ ‖z‖ < B)
    (hT : ∀ z ∈ spectrum ℂ T, z.im = 0 ∧ ‖z‖ < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ U ∩ resolventSet ℂ T)
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ U ∩ resolventSet ℂ T) :
    R.comp (cutoffCircleOperator U η B) = (cutoffCircleOperator T η B).comp R := by
  obtain ⟨hu₁, hu₂⟩ := cutoffCircle_spheres_resolvent U η B (hη.trans hB) hU hp.1 hn.1
  obtain ⟨ht₁, ht₂⟩ := cutoffCircle_spheres_resolvent T η B (hη.trans hB) hT hp.2 hn.2
  exact twoCircleResolvent_intertwine U T R h _ _ _ _ (by linarith) (by linarith)
    (fun z hz ↦ ⟨hu₁ z hz, ht₁ z hz⟩) (fun z hz ↦ ⟨hu₂ z hz, ht₂ z hz⟩)

namespace AmbientKernel
universe u v
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Z : Type v} [MetricSpace Z] [CompactSpace Z]
variable (e : C(X, Z)) (μ : Measure X) [IsProbabilityMeasure μ]

theorem restriction_cutoffCircle (he : Isometry e) (η B : ℝ) (hη : 0 < η) (hB : η < B)
    (hd : diam (univ : Set X) < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ)) :
    (restriction e μ).comp (cutoffCircleOperator (ambientOperator e μ) η B) =
      (closedEigenSpan (ComplexKernel.distanceOperator μ) {a | η < ‖a‖}).starProjection.comp
        (restriction e μ) := by
  have ht : ∀ z ∈ spectrum ℂ (ComplexKernel.distanceOperator μ), z.im = 0 ∧ ‖z‖ < B := by
    intro z hz
    obtain ⟨hi, hh⟩ := ComplexKernel.distanceOperator_spectrum_bound μ hz
    exact ⟨hi, hh.trans_lt hd⟩
  have hu : ∀ z ∈ spectrum ℂ (ambientOperator e μ), z.im = 0 ∧ ‖z‖ < B := by
    intro z hz
    by_cases hzero : z = 0
    · simp [hzero, hη.trans hB]
    · apply ht z
      have hh : z ∈ spectrum ℂ (ambientOperator e μ) \ {0} := ⟨hz, hzero⟩
      rw [ambient_nonzero_spectrum_eq e μ he] at hh
      exact hh.1
  have hp' := (nonzero_resolventSet_iff e μ he (η : ℂ) (by exact_mod_cast ne_of_gt hη)).mpr hp
  have hn' := (nonzero_resolventSet_iff e μ he ((-η : ℝ) : ℂ)
    (by exact_mod_cast neg_ne_zero.mpr (ne_of_gt hη))).mpr hn
  rw [← ComplexKernel.distance_cutoffCircle_eq_starProjection μ η B hη hB hd hp hn]
  exact cutoffCircle_intertwine _ _ _ (restriction_intertwine e μ he) η B hη hB hu ht
    ⟨hp', hp⟩ ⟨hn', hn⟩

theorem restriction_cutoffCircle_explicit (he : Isometry e) (η : ℝ) (hη : 0 < η)
    (hp : (η : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ)) :
    (restriction e μ).comp (cutoffCircleOperator (ambientOperator e μ) η
      (diam (univ : Set X) + η + 1)) =
      (closedEigenSpan (ComplexKernel.distanceOperator μ) {a | η < ‖a‖}).starProjection.comp
        (restriction e μ) := by
  apply restriction_cutoffCircle e μ he η _ hη _ _ hp hn
  · linarith [diam_nonneg (s := (univ : Set X))]
  · linarith
end AmbientKernel
end PaperN.PartII
