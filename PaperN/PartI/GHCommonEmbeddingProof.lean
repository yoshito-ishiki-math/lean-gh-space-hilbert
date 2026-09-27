import PaperN.PartI.CommonBaseLimit
import Mathlib.Topology.Sets.VietorisTopology

namespace PaperN.PartI
open Set Metric GromovHausdorff Filter TopologicalSpace
open scoped Topology

/-- A GH-convergent sequence admits one compact ambient, using fixed-base gluing. -/
theorem ghCommonEmbeddingInput_proved : GHCommonEmbeddingInput.{u} := by
  intro Xs X h
  let Z := BasedAmbient.JointCarrier X (fun n ↦ Xs n)
  let e : X → Z := BasedAmbient.jointBase X (fun n ↦ Xs n)
  let es : ∀ n, Xs n → Z := BasedAmbient.jointMap X (fun n ↦ Xs n)
  have he : Isometry e := BasedAmbient.jointBase_isometry X (fun n ↦ Xs n)
  have hes : ∀ n, Isometry (es n) := BasedAmbient.jointMap_isometry X (fun n ↦ Xs n)
  let K : NonemptyCompacts Z := ⟨⟨range e, isCompact_range he.continuous⟩, range_nonempty e⟩
  let Ks : ℕ → NonemptyCompacts Z := fun n ↦
    ⟨⟨range (es n), isCompact_range (hes n).continuous⟩, range_nonempty (es n)⟩
  have hK : Tendsto Ks atTop (𝓝 K) :=
    tendsto_iff_dist_tendsto_zero.mpr (BasedAmbient.joint_hausdorffConverges X (fun n ↦ Xs n) h)
  let S : Set Z := ⋃ L ∈ insert K (range Ks), (L : Set Z)
  have hS : IsCompact S := NonemptyCompacts.isCompact_biUnion_coe_of_isCompact hK.isCompact_insert_range
  have heS : ∀ x, e x ∈ S := fun x ↦ mem_iUnion.mpr ⟨K,
    mem_iUnion.mpr ⟨mem_insert _ _, mem_range_self x⟩⟩
  have hesS : ∀ n x, es n x ∈ S := fun n x ↦ mem_iUnion.mpr ⟨Ks n,
    mem_iUnion.mpr ⟨mem_insert_of_mem _ (mem_range_self n), mem_range_self x⟩⟩
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let C : CommonRealization Xs X := {
    Carrier := S
    metric := inferInstance
    compact := inferInstance
    seqMap := fun n x ↦ ⟨es n x, hesS n x⟩
    limitMap := fun x ↦ ⟨e x, heS x⟩
    seq_isometry := fun n ↦ Isometry.of_dist_eq (fun x y ↦ (hes n).dist_eq x y)
    limit_isometry := Isometry.of_dist_eq (fun x y ↦ he.dist_eq x y) }
  refine ⟨C, ?_⟩
  have hh := BasedAmbient.joint_hausdorffConverges X (fun n ↦ Xs n) h
  unfold CommonRealization.HausdorffConverges
  convert hh using 1
  funext n
  have hv : Isometry (Subtype.val : S → Z) := Isometry.of_dist_eq (fun _ _ ↦ rfl)
  rw [← hausdorffDist_image hv]
  simp only [← range_comp]
  rfl
end PaperN.PartI
