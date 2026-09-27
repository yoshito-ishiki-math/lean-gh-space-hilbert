import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.ContinuousMap.Compact

/-! The full self-isometry group equipped with the uniform metric. -/
namespace PaperN.PartI
open scoped BoundedContinuousFunction
variable {X : Type*} [MetricSpace X] [CompactSpace X]

noncomputable def isometryBCF (g : X ≃ᵢ X) : X →ᵇ X :=
  BoundedContinuousFunction.mkOfCompact ⟨g, g.continuous⟩

@[simp] lemma isometryBCF_apply (g : X ≃ᵢ X) (x : X) : isometryBCF g x = g x := rfl

lemma isometryBCF_injective : Function.Injective (isometryBCF (X := X)) := by
  intro g h heq
  ext x
  exact congrArg (fun f : X →ᵇ X ↦ f x) heq

noncomputable instance isometryGroupMetric : MetricSpace (X ≃ᵢ X) :=
  MetricSpace.induced isometryBCF isometryBCF_injective inferInstance

lemma isometry_isometryBCF : Isometry (isometryBCF (X := X)) := fun _ _ ↦ rfl

end PaperN.PartI
