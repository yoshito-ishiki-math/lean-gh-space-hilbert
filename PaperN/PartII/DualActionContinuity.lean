import PaperN.PartII.DualEquivariance
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace PaperN.PartII
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {T : Type*} [TopologicalSpace T]

/-- Operator-norm continuous orthogonal families have continuous inverse operators. -/
theorem continuous_orthogonal_inverse (U : T → E ≃ₗᵢ[ℝ] E)
    (hU : Continuous fun t ↦ (U t).toContinuousLinearEquiv.toContinuousLinearMap) :
    Continuous fun t ↦ (U t).symm.toContinuousLinearEquiv.toContinuousLinearMap := by
  have h := (ContinuousLinearMap.adjoint : (E →L[ℝ] E) ≃ₗᵢ⋆[ℝ] (E →L[ℝ] E)).continuous.comp hU
  simpa only [Function.comp_def, LinearIsometryEquiv.adjoint_eq_symm] using h

/-- Joint continuity of the sphere action for every continuous orthogonal family. -/
theorem continuous_orthogonalSphereAction (U : T → E ≃ₗᵢ[ℝ] E)
    (hU : Continuous fun t ↦ (U t).toContinuousLinearEquiv.toContinuousLinearMap) :
    Continuous (fun z : T × C(Metric.sphere (0 : E) 1, ℝ) ↦
      orthogonalSphereAction (U z.1) z.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hi := continuous_orthogonal_inverse U hU
  have he : Continuous (fun z : (T × C(Metric.sphere (0 : E) 1, ℝ)) ×
      Metric.sphere (0 : E) 1 ↦ (U z.1.1).symm z.2.val) :=
    (hi.comp (continuous_fst.comp continuous_fst)).clm_apply
      (continuous_subtype_val.comp continuous_snd)
  exact continuous_eval.comp
    ((continuous_snd.comp continuous_fst).prodMk (he.subtype_mk _))

/-- The usual operator-norm topology on the orthogonal group. -/
noncomputable abbrev orthogonalOperatorTopology : TopologicalSpace (E ≃ₗᵢ[ℝ] E) :=
  TopologicalSpace.induced (fun U : E ≃ₗᵢ[ℝ] E ↦
    U.toContinuousLinearEquiv.toContinuousLinearMap) inferInstance

/-- The orthogonal action is jointly continuous in the operator-norm topology. -/
theorem continuous_orthogonalSphereAction_operatorTopology :
    letI : TopologicalSpace (E ≃ₗᵢ[ℝ] E) := orthogonalOperatorTopology
    Continuous (fun z : (E ≃ₗᵢ[ℝ] E) × C(Metric.sphere (0 : E) 1, ℝ) ↦
      orthogonalSphereAction z.1 z.2) := by
  letI : TopologicalSpace (E ≃ₗᵢ[ℝ] E) := orthogonalOperatorTopology
  exact continuous_orthogonalSphereAction id continuous_induced_dom

end PaperN.PartII
