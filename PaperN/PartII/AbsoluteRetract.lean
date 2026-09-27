import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Algebra.MulAction

namespace PaperN.PartII
open TopologicalSpace
universe u v w g

/-- Absolute retract in the metrizable category, with the ambient universe explicit. -/
def IsAbsoluteRetract (X : Type u) [TopologicalSpace X] : Prop :=
  MetrizableSpace X ∧ ∀ (Y : Type v) [TopologicalSpace Y] [MetrizableSpace Y]
    (e : X → Y), Topology.IsClosedEmbedding e →
      ∃ r : Y → X, Continuous r ∧ Function.LeftInverse r e

/-- Equivariant absolute retract, using closed equivariant embeddings and retractions. -/
def IsEquivariantAbsoluteRetract (G : Type g) [Group G] [TopologicalSpace G]
    (X : Type u) [TopologicalSpace X] [MulAction G X] : Prop :=
  MetrizableSpace X ∧ ContinuousSMul G X ∧
    ∀ (Y : Type v) [TopologicalSpace Y] [MetrizableSpace Y] [MulAction G Y]
      [ContinuousSMul G Y] (e : X → Y), Topology.IsClosedEmbedding e →
      (∀ (a : G) x, e (a • x) = a • e x) →
      ∃ r : Y → X, Continuous r ∧ Function.LeftInverse r e ∧
        ∀ (a : G) y, r (a • y) = a • r y

/-- AR status is unchanged when the target is replaced by a homeomorphic space. -/
theorem IsAbsoluteRetract.of_homeomorph
    {X : Type u} {Z : Type w} [TopologicalSpace X] [TopologicalSpace Z]
    (hX : IsAbsoluteRetract.{u,v} X) (h : X ≃ₜ Z) :
    IsAbsoluteRetract.{w,v} Z := by
  letI : MetrizableSpace X := hX.1
  refine ⟨h.symm.isEmbedding.metrizableSpace, ?_⟩
  intro Y _ _ e he
  obtain ⟨r, hr, hre⟩ := hX.2 Y (e ∘ h) (he.comp h.isClosedEmbedding)
  refine ⟨h ∘ r, h.continuous.comp hr, ?_⟩
  intro z
  have hz := hre (h.symm z)
  simpa only [Function.comp_apply, h.apply_symm_apply] using congrArg h hz

/-- A form convenient for transporting the metrizable AR property across quotient models. -/
theorem isAbsoluteRetract_homeomorph_iff
    {X : Type u} {Z : Type w} [TopologicalSpace X] [TopologicalSpace Z]
    (h : X ≃ₜ Z) : IsAbsoluteRetract.{u,v} X ↔ IsAbsoluteRetract.{w,v} Z :=
  ⟨fun hx ↦ hx.of_homeomorph h, fun hz ↦ hz.of_homeomorph h.symm⟩

end PaperN.PartII
