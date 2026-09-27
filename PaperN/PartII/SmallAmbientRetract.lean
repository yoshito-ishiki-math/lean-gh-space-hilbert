import PaperN.PartII.AbsoluteNeighborhoodRetract
import Mathlib.Topology.Instances.Shrink
import Mathlib.Topology.MetricSpace.PiNat

namespace PaperN.PartII
open TopologicalSpace
universe v

/-- An AR for small ambient spaces retracts from any ambient whose carrier is small. -/
theorem IsAbsoluteRetract.retraction_of_small
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [MetrizableSpace Y]
    [Small.{0} Y] (h : IsAbsoluteRetract.{_,0} X)
    (e : X → Y) (he : Topology.IsClosedEmbedding e) :
    ∃ r : Y → X, Continuous r ∧ Function.LeftInverse r e := by
  let k := Shrink.homeomorph (X := Y)
  letI : MetrizableSpace (Shrink.{0} Y) := k.symm.isEmbedding.metrizableSpace
  obtain ⟨r, hr, hre⟩ := h.2 (Shrink.{0} Y) (k ∘ e) (k.isClosedEmbedding.comp he)
  exact ⟨r ∘ k, hr.comp k.continuous, hre⟩

/-- The neighbourhood retraction also transports through a small ambient model. -/
theorem IsAbsoluteNeighborhoodRetract.retraction_of_small
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [MetrizableSpace Y]
    [Small.{0} Y] (h : IsAbsoluteNeighborhoodRetract.{_,0} X)
    (e : X → Y) (he : Topology.IsClosedEmbedding e) :
    ∃ U : Set Y, IsOpen U ∧ Set.range e ⊆ U ∧
      ∃ r : U → X, Continuous r ∧ ∀ x (hx : e x ∈ U), r ⟨e x, hx⟩ = x := by
  let k := Shrink.homeomorph (X := Y)
  letI : MetrizableSpace (Shrink.{0} Y) := k.symm.isEmbedding.metrizableSpace
  obtain ⟨V, hV, hv, r, hr, hre⟩ :=
    h.2 (Shrink.{0} Y) (k ∘ e) (k.isClosedEmbedding.comp he)
  refine ⟨k ⁻¹' V, hV.preimage k.continuous, ?_,
    (fun y ↦ r ⟨k y.val, y.property⟩), ?_, ?_⟩
  · rintro y ⟨x, rfl⟩
    exact hv ⟨x, rfl⟩
  · exact hr.comp ((k.continuous.comp continuous_subtype_val).subtype_mk _)
  · intro x hx
    exact hre x hx

/-- Every separable metric carrier admits a universe-zero model via the Hilbert cube. -/
theorem small_separable_metric (Y : Type*) [MetricSpace Y] [SeparableSpace Y] :
    Small.{0} Y := by
  obtain ⟨f, hf⟩ := Metric.PiNatEmbed.exists_embedding_to_hilbert_cube (X := Y)
  exact small_of_injective hf.injective

/-- Universe-zero ANR status implies separable ANR status in every ambient universe. -/
theorem IsAbsoluteNeighborhoodRetract.separable_allUniverses
    {X : Type*} [TopologicalSpace X] (h : IsAbsoluteNeighborhoodRetract.{_,0} X) :
    IsSeparableAbsoluteNeighborhoodRetract.{_,v} X := by
  refine ⟨h.1, ?_⟩
  intro Y _ _ _ e he
  letI := TopologicalSpace.metrizableSpaceMetric Y
  letI : Small.{0} Y := small_separable_metric Y
  exact h.retraction_of_small e he
end PaperN.PartII
