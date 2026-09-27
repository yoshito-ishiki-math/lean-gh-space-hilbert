import PaperN.PartII.AmbientKernel
import PaperN.PartII.FactorSpectrum
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

namespace PaperN.PartII.AmbientKernel
open MeasureTheory Metric Set
open scoped Topology
universe u v
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Z : Type v} [MetricSpace Z] [CompactSpace Z]
variable (e : C(X, Z)) (μ : Measure X) [IsProbabilityMeasure μ]

theorem distanceToContinuous_compact : IsCompactOperator (distanceToContinuous e μ) := by
  let E := ContinuousMap.linearIsometryBoundedOfCompact Z ℂ ℂ
  let S : Set (BoundedContinuousFunction Z ℂ) := (fun f ↦ E (distanceToContinuous e μ f)) '' closedBall 0 1
  have hb : ∀ g ∈ S, ∃ f : Lp ℂ 2 μ, ‖f‖ ≤ 1 ∧ E (distanceToContinuous e μ f) = g := by
    rintro g ⟨f, hf, rfl⟩
    exact ⟨f, by simpa using hf, rfl⟩
  have hc : IsCompact (closure S) := by
    apply BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) (diam (univ : Set Z)))
      (isCompact_closedBall _ _)
    · intro g z hg
      obtain ⟨f, hf, rfl⟩ := hb g hg
      rw [mem_closedBall, dist_eq_norm]
      change ‖distanceValue e μ f z - 0‖ ≤ _
      simpa using (distanceValue_bound e μ f z).trans
        (mul_le_of_le_one_right diam_nonneg hf)
    · refine Metric.equicontinuous_of_continuity_modulus id (by exact continuous_id.continuousAt)
        ((↑) : S → Z → ℂ) ?_
      intro z w g
      obtain ⟨f, hf, hfg⟩ := hb g g.property
      change dist (g.val z) (g.val w) ≤ dist z w
      rw [← hfg]
      exact (distanceValue_lipschitz e μ f).dist_le_mul z w |>.trans
        (by simpa using mul_le_of_le_one_left dist_nonneg hf)
  refine (isCompactOperator_iff_exists_mem_nhds_image_subset_compact _).mpr
    ⟨closedBall 0 1, closedBall_mem_nhds _ zero_lt_one,
      E.symm '' closure S, hc.image E.symm.continuous, ?_⟩
  rintro g ⟨f, hf, rfl⟩
  exact ⟨E (distanceToContinuous e μ f), subset_closure ⟨f, hf, rfl⟩, E.symm_apply_apply _⟩

theorem ambientOperator_compact : IsCompactOperator (ambientOperator e μ) :=
  (distanceToContinuous_compact e μ).comp_clm (restriction e μ)

theorem distanceOperator_compact (he : Isometry e) :
    IsCompactOperator (ComplexKernel.distanceOperator μ) := by
  rw [← restriction_extension e μ he]
  exact (distanceToContinuous_compact e μ).clm_comp (restriction e μ)

theorem ambient_nonzero_spectrum_eq (he : Isometry e) :
    spectrum ℂ (ambientOperator e μ) \ {0} =
      spectrum ℂ (ComplexKernel.distanceOperator μ) \ {0} := by
  have h := factor_nonzero_spectrum_eq (distanceToContinuous e μ) (restriction e μ)
    (ambientOperator_compact e μ)
    ((distanceToContinuous_compact e μ).clm_comp (restriction e μ))
  change spectrum ℂ (ambientOperator e μ) \ {0} =
    spectrum ℂ ((restriction e μ).comp (distanceToContinuous e μ)) \ {0} at h
  rwa [restriction_extension e μ he] at h

end PaperN.PartII.AmbientKernel
