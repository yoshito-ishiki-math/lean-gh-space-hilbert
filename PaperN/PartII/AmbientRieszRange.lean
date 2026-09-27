import PaperN.PartII.CutoffRieszInput
import PaperN.PartII.AmbientSelectedEquivalence
import PaperN.PartII.CircleIntertwining
import PaperN.PartII.AmbientCircleRangeProof

namespace PaperN.PartII.AmbientKernel
open MeasureTheory Metric Set
universe u v
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Z : Type v} [MetricSpace Z] [CompactSpace Z]
variable (e : C(X,Z)) (μ : Measure X) [IsProbabilityMeasure μ]

theorem ambient_cutoff_generalized_eq (he : Isometry e) (η : ℝ) (hη : 0 < η) :
    (⨆ a : ℂ, ⨆ (_ : η < ‖a‖), Module.End.maxGenEigenspace (ambientOperator e μ).toLinearMap a) =
      ambientAlgebraicCutoff e μ η := by
  apply iSup_congr
  intro a
  apply iSup_congr
  intro ha
  exact ambient_maxGenEigenspace e μ he a (norm_pos_iff.mp (hη.trans ha))

theorem ambient_cutoffCircle_range
    (he : Isometry e) (η B : ℝ) (hη : 0 < η) (hB : η < B)
    (hd : diam (univ : Set X) < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ)) :
    LinearMap.range (cutoffCircleOperator (ambientOperator e μ) η B).toLinearMap =
      ambientAlgebraicCutoff e μ η := by
  exact ambient_cutoffCircle_range_proved e μ he η B hη hB hd hp hn

noncomputable def restrictionCircleRangeEquiv
    (he : Isometry e) (η B : ℝ) (hη : 0 < η) (hB : η < B)
    (hd : diam (univ : Set X) < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ)) :
    LinearMap.range (cutoffCircleOperator (ambientOperator e μ) η B).toLinearMap ≃ₗ[ℂ]
      complexAlgebraicCutoff (ComplexKernel.distanceOperator μ) η :=
  (LinearEquiv.ofEq _ _ (ambient_cutoffCircle_range e μ  he η B hη hB hd hp hn)).trans
    (restrictionCutoffEquiv e μ he η hη)

theorem restrictionCircleRangeEquiv_apply
    (he : Isometry e) (η B : ℝ) (hη : 0 < η) (hB : η < B)
    (hd : diam (univ : Set X) < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (f : LinearMap.range (cutoffCircleOperator (ambientOperator e μ) η B).toLinearMap) :
    (restrictionCircleRangeEquiv e μ  he η B hη hB hd hp hn f : Lp ℂ 2 μ) =
      restriction e μ f := rfl
theorem ambient_cutoffCircle_idempotent
    (he : Isometry e) (η B : ℝ) (hη : 0 < η) (hB : η < B)
    (hd : diam (univ : Set X) < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ)) :
    (cutoffCircleOperator (ambientOperator e μ) η B).comp
      (cutoffCircleOperator (ambientOperator e μ) η B) =
      cutoffCircleOperator (ambientOperator e μ) η B := by
  let P := cutoffCircleOperator (ambientOperator e μ) η B
  have hu : ∀ z ∈ spectrum ℂ (ambientOperator e μ), z.im = 0 ∧ ‖z‖ < B := by
    intro z hz
    by_cases hzero : z = 0
    · simp [hzero, hη.trans hB]
    · have hh : z ∈ spectrum ℂ (ambientOperator e μ) \ {0} := ⟨hz,hzero⟩
      rw [ambient_nonzero_spectrum_eq e μ he] at hh
      obtain ⟨hi,hb⟩ := ComplexKernel.distanceOperator_spectrum_bound μ hh.1
      exact ⟨hi,hb.trans_lt hd⟩
  have hp' := (nonzero_resolventSet_iff e μ he (η : ℂ) (by exact_mod_cast ne_of_gt hη)).mpr hp
  have hn' := (nonzero_resolventSet_iff e μ he ((-η : ℝ) : ℂ)
    (by exact_mod_cast neg_ne_zero.mpr (ne_of_gt hη))).mpr hn
  have hfix : ambientAlgebraicCutoff e μ η ≤ (P - ContinuousLinearMap.id ℂ C(Z,ℂ)).ker := by
    apply iSup_le
    intro a
    apply iSup_le
    intro ha f hf
    have hv := Module.End.mem_eigenspace_iff.mp hf
    change ambientOperator e μ f = a • f at hv
    change P f - f = 0
    dsimp [P]
    rw [cutoffCircle_apply_eigenvector _ η B hη hB hu hp' hn' a f hv,
      if_pos (show η < ‖a‖ from ha), sub_self]
  apply ContinuousLinearMap.ext
  intro f
  have hmem : P f ∈ ambientAlgebraicCutoff e μ η := by
    rw [← ambient_cutoffCircle_range e μ  he η B hη hB hd hp hn]
    exact ⟨f,rfl⟩
  have hh := hfix hmem
  change P (P f) - P f = 0 at hh
  exact sub_eq_zero.mp hh
end PaperN.PartII.AmbientKernel
