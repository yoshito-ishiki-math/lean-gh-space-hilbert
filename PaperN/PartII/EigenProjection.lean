import PaperN.PartII.CircleOperator

namespace PaperN.PartII
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem idempotent_of_dense_eigenspaces (U P : E →L[ℂ] E)
    (hd : (⨆ a : ℂ, Module.End.eigenspace U.toLinearMap a).topologicalClosure = ⊤)
    (hp : ∀ (a : ℂ) (v : E), U v = a • v → P v = 0 ∨ P v = v) :
    P.comp P = P := by
  let Q := P.comp P - P
  have hs : (⨆ a : ℂ, Module.End.eigenspace U.toLinearMap a) ≤ Q.ker := by
    apply iSup_le
    intro a v hv
    have he := Module.End.mem_eigenspace_iff.mp hv
    change U v = a • v at he
    change P (P v) - P v = 0
    rcases hp a v he with h | h
    · rw [h, map_zero, sub_self]
    · simp only [h, sub_self]
  have hc := (⨆ a : ℂ, Module.End.eigenspace U.toLinearMap a).topologicalClosure_minimal hs Q.isClosed_ker
  rw [hd] at hc
  apply ContinuousLinearMap.ext
  intro v
  have hv := hc (show v ∈ (⊤ : Submodule ℂ E) from trivial)
  change P (P v) - P v = 0 at hv
  exact sub_eq_zero.mp hv

open Metric Set in
theorem circleResolvent_idempotent [CompleteSpace E] (U : E →L[ℂ] E) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ U)
    (hd : (⨆ a : ℂ, Module.End.eigenspace U.toLinearMap a).topologicalClosure = ⊤)
    :
    (circleResolvent U c r).comp (circleResolvent U c r) = circleResolvent U c r := by
  apply idempotent_of_dense_eigenspaces U _ hd
  intro a v hv
  by_cases hzero : v = 0
  · left; simp [hzero]
  have he : Module.End.HasEigenvalue U.toLinearMap a :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hv, hzero⟩
  by_cases hi : a ∈ ball c r
  · exact Or.inr (circleResolvent_fixes_inside U a c r hz hi v hv)
  · have ho : a ∉ closedBall c r := by
      intro hcl
      have hdist : dist a c = r := le_antisymm hcl (le_of_not_gt hi)
      have hspec : a ∈ spectrum ℂ U := by
        rw [ContinuousLinearMap.spectrum_eq]
        exact he.mem_spectrum
      exact hspec (hz a (mem_sphere.mpr hdist))
    exact Or.inl (circleResolvent_kills_outside U a c r hr hz ho v hv)
open Metric Set in
theorem circleResolvent_idempotent_of_compact_symmetric
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : H →L[ℂ] H) (hc : IsCompactOperator U) (hs : U.toLinearMap.IsSymmetric)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ U) :
    (circleResolvent U c r).comp (circleResolvent U c r) = circleResolvent U c r := by
  apply circleResolvent_idempotent U c r hr hz
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure]
  exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hs

namespace ComplexKernel
open MeasureTheory Metric Set
universe u
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]

theorem distance_circleResolvent_idempotent (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ (distanceOperator μ)) :
    (circleResolvent (distanceOperator μ) c r).comp (circleResolvent (distanceOperator μ) c r) =
      circleResolvent (distanceOperator μ) c r :=
  circleResolvent_idempotent_of_compact_symmetric _
    (AmbientKernel.distanceOperator_compact (ContinuousMap.id X) μ isometry_id)
    (distanceOperator_symmetric μ) c r hr hz
end ComplexKernel
end PaperN.PartII
