import PaperN.PartII.AmbientSelectedEquivalence
import PaperN.PartII.CompactSelectorFiniteRange
import PaperN.PartII.CircleSquareFactorization
import PaperN.PartII.SymmetricFactorSquareRange
import PaperN.PartII.SelectedSquareRange

namespace PaperN.PartII.AmbientKernel
open MeasureTheory Metric Set
universe u v
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Z : Type v} [MetricSpace Z] [CompactSpace Z]
variable (e : C(X,Z)) (μ : Measure X) [IsProbabilityMeasure μ]

theorem ambient_cutoffCircle_range_proved
    (he : Isometry e) (η B : ℝ) (hη : 0 < η) (hB : η < B)
    (hd : diam (univ : Set X) < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ)) :
    LinearMap.range (cutoffCircleOperator (ambientOperator e μ) η B).toLinearMap =
      ambientAlgebraicCutoff e μ η := by
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
  have ht : ∀ z ∈ spectrum ℂ (ComplexKernel.distanceOperator μ), z.im = 0 ∧ ‖z‖ < B := by
    intro z hz
    obtain ⟨hi,hb⟩ := ComplexKernel.distanceOperator_spectrum_bound μ hz
    exact ⟨hi,hb.trans_lt hd⟩
  have hinter := restriction_cutoffCircle e μ he η B hη hB hd hp hn
  rw [← ComplexKernel.distance_cutoffCircle_eq_starProjection μ η B hη hB hd hp hn] at hinter
  have hrange := cutoffCircle_range_eq_eigenspaces (ComplexKernel.distanceOperator μ)
    (distanceOperator_compact (ContinuousMap.id X) μ isometry_id)
    (ComplexKernel.distanceOperator_symmetric μ) η B hη hB ht hp hn
  have hzero : (0 : ℂ) ∉ {a | η < ‖a‖} := by simpa using (not_lt.mpr hη.le)
  have hsq := cutoffCircle_range_le_square_range (ambientOperator e μ) η B hη hB hu hp' hn'
  have hesq := selectedEigenspaces_le_square_range (ambientOperator e μ).toLinearMap
    {a | η < ‖a‖} hzero
  apply le_antisymm
  · intro y hy
    obtain ⟨x,hx⟩ := hy
    change cutoffCircleOperator (ambientOperator e μ) η B x = y at hx
    have hry : restriction e μ y ∈ selectedEigenspaces (ComplexKernel.distanceOperator μ).toLinearMap
        {a | η < ‖a‖} := by
      change restriction e μ y ∈ (⨆ a : ℂ, ⨆ (_ : η < ‖a‖), Module.End.eigenspace (ComplexKernel.distanceOperator μ).toLinearMap a)
      rw [← hrange]
      refine ⟨restriction e μ x, ?_⟩
      have hi := congrArg (fun A : C(Z,ℂ) →L[ℂ] Lp ℂ 2 μ ↦ A x) hinter
      change restriction e μ (cutoffCircleOperator (ambientOperator e μ) η B x) =
        cutoffCircleOperator (ComplexKernel.distanceOperator μ) η B (restriction e μ x) at hi
      rw [hx] at hi
      exact hi.symm
    rw [← restriction_map_selected e μ he {a | η < ‖a‖} hzero] at hry
    obtain ⟨v,hv,hvR⟩ := hry
    change restriction e μ v = restriction e μ y at hvR
    have hdiff : y-v ∈ LinearMap.range ((ambientOperator e μ).comp (ambientOperator e μ)).toLinearMap :=
      (LinearMap.range _).sub_mem (hsq ⟨x,hx⟩) (hesq hv)
    have hz : restriction e μ (y-v) = 0 := by
      rw [map_sub, hvR, sub_self]
    have heq := restriction_zero_on_ambient_square_range e μ he (y-v) hdiff hz
    rw [sub_eq_zero.mp heq]
    exact hv
  · apply iSup_le
    intro a
    apply iSup_le
    intro ha f hf
    have hv := Module.End.mem_eigenspace_iff.mp hf
    refine ⟨f, ?_⟩
    exact (cutoffCircle_apply_eigenvector _ η B hη hB hu hp' hn' a f hv).trans (if_pos ha)
end PaperN.PartII.AmbientKernel
