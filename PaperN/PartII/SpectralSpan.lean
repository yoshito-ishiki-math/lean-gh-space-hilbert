import PaperN.PartII.ProfileApproximation
import PaperN.PartII.SpectralApproximationStatements
import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace PaperN.PartII
open MeasureTheory Set Module
universe u
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]

theorem continuous_kernel_zero (f : Lp ℝ 2 μ) (hf : distanceOperator μ f = 0) :
    distanceToContinuous μ f = 0 := by
  apply continuousToL2_injective μ
  change distanceOperator μ f = continuousToL2 μ 0
  simpa only [map_zero] using hf

omit [μ.IsOpenPosMeasure] in
theorem distanceToContinuous_eigen_mem (f : Lp ℝ 2 μ) (a : ℝ) (ha : a ≠ 0)
    (hf : distanceOperator μ f = a • f) :
    distanceToContinuous μ f ∈ continuousEigenvectors μ := by
  refine ⟨a,ha,?_⟩
  change distanceOperator μ (distanceOperator μ f) = a • distanceOperator μ f
  rw [hf, map_smul, hf]

/-- The compact self-adjoint spectral theorem, transferred from L² to the uniform topology. -/
theorem distanceToContinuous_mem_uniformSpectralSpan
    (hc : IsCompactOperator (distanceOperator μ)) (ha : IsSelfAdjoint (distanceOperator μ))
    (f : Lp ℝ 2 μ) : distanceToContinuous μ f ∈ uniformSpectralSpan μ := by
  let T := distanceOperator μ
  let U := uniformSpectralSpan μ
  let V : Submodule ℝ (Lp ℝ 2 μ) := U.comap (distanceToContinuous μ).toLinearMap
  have hV : IsClosed (V : Set (Lp ℝ 2 μ)) :=
    (Submodule.isClosed_topologicalClosure _).preimage (distanceToContinuous μ).continuous
  have hle : (⨆ a : ℝ, Module.End.eigenspace T.toLinearMap a) ≤ V := by
    apply iSup_le
    intro a f hf
    have he := Module.End.mem_eigenspace_iff.mp hf
    change distanceToContinuous μ f ∈ U
    by_cases hz : a = 0
    · have hk : distanceOperator μ f = 0 := by simpa [hz] using he
      rw [continuous_kernel_zero μ f hk]
      exact U.zero_mem
    · exact (Submodule.le_topologicalClosure _) (Submodule.subset_span (distanceToContinuous_eigen_mem μ f a hz he))
  have htop : (⨆ a : ℝ, Module.End.eigenspace T.toLinearMap a).topologicalClosure = ⊤ := by
    apply Submodule.orthogonal_eq_bot_iff.mp
    rw [Submodule.orthogonal_closure]
    exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc ha.isSymmetric
  have h := Submodule.topologicalClosure_minimal _ hle hV
  rw [htop] at h
  exact h (Submodule.mem_top)

/-- Every distance profile is in the uniform closed span of nonzero eigenfunctions. -/
theorem distanceProfile_mem_uniformSpectralSpan
    (hc : IsCompactOperator (distanceOperator μ)) (ha : IsSelfAdjoint (distanceOperator μ))
    (x : X) : distanceProfile x ∈ uniformSpectralSpan μ := by
  apply closure_minimal (s := range (distanceToContinuous μ))
    (t := (uniformSpectralSpan μ : Set C(X, ℝ))) ?_
    (Submodule.isClosed_topologicalClosure _) (distanceProfile_mem_closure_range μ x)
  rintro _ ⟨f,rfl⟩
  exact distanceToContinuous_mem_uniformSpectralSpan μ hc ha f
end PaperN.PartII
