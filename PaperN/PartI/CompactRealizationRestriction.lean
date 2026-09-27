import PaperN.PartI.CouplingCommonAmbient
import PaperN.PartI.CommonRealization
import Mathlib.Topology.Sets.VietorisTopology

namespace PaperN.PartI
open Set Metric Filter TopologicalSpace MeasureTheory
open scoped Topology
universe u

/-- A simultaneous realization with vanishing Hausdorff error can be restricted
 to a compact union without changing either distance. -/
theorem compactRealization_of_common_ambient
    (Xs : ℕ → MeasuredCompact.{u}) (X : MeasuredCompact.{u})
    {Z : Type u} [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (e : X → Z) (es : ∀ n, Xs n → Z) (he : Isometry e)
    (hes : ∀ n, Isometry (es n))
    (hh : Tendsto (fun n ↦ hausdorffDist (range e) (range (es n))) atTop (𝓝 0))
    (hp : Tendsto (fun n ↦ levyProkhorovDist (Measure.map e X.measure)
      (Measure.map (es n) (Xs n).measure)) atTop (𝓝 0)) :
    ∃ C : CommonRealization Xs X, C.HausdorffConverges ∧ C.ProkhorovConverges := by
  let K : NonemptyCompacts Z := ⟨⟨range e, isCompact_range he.continuous⟩, range_nonempty e⟩
  let Ks : ℕ → NonemptyCompacts Z := fun n ↦
    ⟨⟨range (es n), isCompact_range (hes n).continuous⟩, range_nonempty (es n)⟩
  have hh' : Tendsto (fun n ↦ hausdorffDist (range (es n)) (range e)) atTop (𝓝 0) := by
    simpa only [hausdorffDist_comm] using hh
  have hK : Tendsto Ks atTop (𝓝 K) := tendsto_iff_dist_tendsto_zero.mpr hh'
  let S : Set Z := ⋃ L ∈ insert K (range Ks), (L : Set Z)
  have hS : IsCompact S := NonemptyCompacts.isCompact_biUnion_coe_of_isCompact hK.isCompact_insert_range
  have heS : ∀ x, e x ∈ S := fun x ↦ mem_iUnion.mpr ⟨K,
    mem_iUnion.mpr ⟨mem_insert _ _, mem_range_self x⟩⟩
  have hesS : ∀ n x, es n x ∈ S := fun n x ↦ mem_iUnion.mpr ⟨Ks n,
    mem_iUnion.mpr ⟨mem_insert_of_mem _ (mem_range_self n), mem_range_self x⟩⟩
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  letI : MeasurableSpace S := borel S
  letI : BorelSpace S := ⟨rfl⟩
  let C : CommonRealization Xs X := {
    Carrier := S
    metric := inferInstance
    compact := inferInstance
    seqMap := fun n x ↦ ⟨es n x, hesS n x⟩
    limitMap := fun x ↦ ⟨e x, heS x⟩
    seq_isometry := fun n ↦ Isometry.of_dist_eq (fun x y ↦ (hes n).dist_eq x y)
    limit_isometry := Isometry.of_dist_eq (fun x y ↦ he.dist_eq x y) }
  have hv : Isometry (Subtype.val : S → Z) := Isometry.of_dist_eq (fun _ _ ↦ rfl)
  refine ⟨C, ?_, ?_⟩
  · unfold CommonRealization.HausdorffConverges
    convert hh' using 1
    funext n
    rw [← hausdorffDist_image hv]
    simp only [← range_comp]
    rfl
  · unfold CommonRealization.ProkhorovConverges
    convert hp using 1
    funext n
    have hvC : Isometry (Subtype.val : C → Z) := hv
    have hid := levyProkhorovDist_map_isometry (Subtype.val : C → Z) hvC
      (C.seqProbability n : Measure C) (C.limitProbability : Measure C)
    rw [← hid]
    change levyProkhorovDist
      (Measure.map Subtype.val (Measure.map (C.seqMap n) (Xs n).measure))
      (Measure.map Subtype.val (Measure.map C.limitMap X.measure)) = _
    rw [Measure.map_map hvC.continuous.measurable (C.seq_isometry n).continuous.measurable,
      Measure.map_map hvC.continuous.measurable C.limit_isometry.continuous.measurable]
    exact levyProkhorovDist_comm _ _

/-- The zero-distance separation problem can be studied in one compact ambient. -/
theorem zero_ghp_compact_common_realization (X Y : MeasuredCompact.{u})
    (h : ghpDist X Y = 0) :
    ∃ C : CommonRealization (fun _ ↦ Y) X,
      C.HausdorffConverges ∧ C.ProkhorovConverges := by
  obtain ⟨Z, m, b, hb, e, es, he, hes, hh, hp⟩ := zero_ghp_common_ambient X Y h
  letI := m
  letI := b
  letI := hb
  exact compactRealization_of_common_ambient (fun _ ↦ Y) X e es he hes hh hp
end PaperN.PartI
