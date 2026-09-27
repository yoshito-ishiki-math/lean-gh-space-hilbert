import PaperN.PartII.NeighborhoodExtensionFactor
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.TietzeExtension

namespace PaperN.PartII
open Set Topology TopologicalSpace
universe v

/-- Separable metrizable ANR targets are neighbourhood extensors, using a
countable Tietze coordinate extension and a metrizable factor. -/
theorem IsAbsoluteNeighborhoodRetract.isAbsoluteNeighborhoodExtensor_of_separable
    {X : Type*} [TopologicalSpace X] [SeparableSpace X]
    (h : IsAbsoluteNeighborhoodRetract.{_,0} X) :
    IsAbsoluteNeighborhoodExtensor.{_,v} X := by
  letI : MetrizableSpace X := h.1
  refine ⟨h.1, ?_⟩
  intro Y _ _ A hA f hf
  by_cases ha : A.Nonempty
  · obtain ⟨a,ha'⟩ := ha
    letI : Nonempty X := ⟨f ⟨a,ha'⟩⟩
    letI := TopologicalSpace.metrizableSpaceMetric X
    letI := TopologicalSpace.metrizableSpaceMetric Y
    obtain ⟨i,hi⟩ := Metric.PiNatEmbed.exists_embedding_to_hilbert_cube (X := X)
    let j : X → ℕ → ℝ := fun x n ↦ (i x n).val
    have hj : IsEmbedding j :=
      (IsEmbedding.piMap (fun _ : ℕ ↦ IsEmbedding.subtypeVal)).comp hi
    obtain ⟨g,hg⟩ := (⟨j ∘ f,hj.continuous.comp hf⟩ : C(A,ℕ → ℝ)).exists_extension'
      hA.isClosedEmbedding_subtypeVal
    apply h.extension_of_factor A f j hj g g.continuous
      (fun a ↦ congrFun hg a) (fun y ↦ Metric.infDist y A) (Metric.continuous_infDist_pt A)
    intro y
    exact (hA.mem_iff_infDist_zero ⟨a,ha'⟩).symm
  · have he : A = ∅ := not_nonempty_iff_eq_empty.mp ha
    subst A
    refine ⟨∅,isOpen_empty,Subset.rfl,(fun x ↦ False.elim x.property),?_,?_⟩
    · exact continuous_of_discreteTopology
    · intro a
      exact False.elim a.property
end PaperN.PartII
