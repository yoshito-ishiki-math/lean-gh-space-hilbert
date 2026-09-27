import PaperN.PartI.IsometryGraph
import PaperN.PartI.CommonRealization

namespace PaperN.PartI
open TopologicalSpace Set Filter Metric
open scoped Topology
universe u
namespace CommonRealization
variable {Xs : ℕ → MeasuredCompact.{u}} {X : MeasuredCompact.{u}}

/-- Entire embedded carriers; no measure support is substituted for the range. -/
noncomputable def seqSet (C : CommonRealization Xs X) (n : ℕ) : NonemptyCompacts C :=
  ⟨⟨range (C.seqMap n), isCompact_range (C.seq_isometry n).continuous⟩, Set.range_nonempty _⟩
noncomputable def limitSet (C : CommonRealization Xs X) : NonemptyCompacts C :=
  ⟨⟨range C.limitMap, isCompact_range C.limit_isometry.continuous⟩, Set.range_nonempty _⟩

noncomputable def seqSetEquiv (C : CommonRealization Xs X) (n : ℕ) : Xs n ≃ᵢ C.seqSet n :=
  (C.seq_isometry n).isometryEquivOnRange
noncomputable def limitSetEquiv (C : CommonRealization Xs X) : X ≃ᵢ C.limitSet :=
  C.limit_isometry.isometryEquivOnRange

noncomputable def seqGraph (C : CommonRealization Xs X) (n : ℕ) (g : Xs n ≃ᵢ Xs n) :
    NonemptyCompacts (C × C) :=
  isometryGraph (C.seqSet n) ((C.seqSetEquiv n).symm.trans (g.trans (C.seqSetEquiv n)))
noncomputable def limitGraph (C : CommonRealization Xs X) (g : X ≃ᵢ X) :
    NonemptyCompacts (C × C) :=
  isometryGraph C.limitSet (C.limitSetEquiv.symm.trans (g.trans C.limitSetEquiv))

/-- The transported graph is exactly the graph in the manuscript's common ambient space. -/
theorem mem_seqGraph (C : CommonRealization Xs X) (n : ℕ) (g : Xs n ≃ᵢ Xs n) (p : C × C) :
    p ∈ C.seqGraph n g ↔ ∃ x : Xs n, (C.seqMap n x, C.seqMap n (g x)) = p := by
  rw [seqGraph, mem_isometryGraph]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(C.seqSetEquiv n).symm x, ?_⟩
    change ((x : C), C.seqMap n (g ((C.seqSetEquiv n).symm x))) = p at hx
    have he : C.seqMap n ((C.seqSetEquiv n).symm x) = (x : C) :=
      congrArg Subtype.val ((C.seqSetEquiv n).apply_symm_apply x)
    simpa only [he] using hx
  · rintro ⟨x, hx⟩
    refine ⟨C.seqSetEquiv n x, ?_⟩
    change (C.seqMap n x, C.seqMap n (g ((C.seqSetEquiv n).symm (C.seqSetEquiv n x)))) = p
    simpa only [IsometryEquiv.symm_apply_apply] using hx

theorem mem_limitGraph (C : CommonRealization Xs X) (g : X ≃ᵢ X) (p : C × C) :
    p ∈ C.limitGraph g ↔ ∃ x : X, (C.limitMap x, C.limitMap (g x)) = p := by
  rw [limitGraph, mem_isometryGraph]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨C.limitSetEquiv.symm x, ?_⟩
    change ((x : C), C.limitMap (g (C.limitSetEquiv.symm x))) = p at hx
    have he : C.limitMap (C.limitSetEquiv.symm x) = (x : C) :=
      congrArg Subtype.val (C.limitSetEquiv.apply_symm_apply x)
    simpa only [he] using hx
  · rintro ⟨x, hx⟩
    refine ⟨C.limitSetEquiv x, ?_⟩
    change (C.limitMap x, C.limitMap (g (C.limitSetEquiv.symm (C.limitSetEquiv x)))) = p
    simpa only [IsometryEquiv.symm_apply_apply] using hx

theorem hausdorffConverges_iff (C : CommonRealization Xs X) :
    C.HausdorffConverges ↔ Tendsto C.seqSet atTop (𝓝 C.limitSet) := by
  rw [tendsto_iff_dist_tendsto_zero]
  rfl

/-- Transport the graph extraction back to the original carriers of the common realization. -/
theorem isometryGraph_subsequence (C : CommonRealization Xs X) (hC : C.HausdorffConverges)
    (gs : ∀ n, Xs n ≃ᵢ Xs n) :
    ∃ (φ : ℕ → ℕ) (g : X ≃ᵢ X), StrictMono φ ∧
      Tendsto (fun n ↦ C.seqGraph (φ n) (gs (φ n))) atTop (𝓝 (C.limitGraph g)) := by
  obtain ⟨φ, g, hφ, hg⟩ := isometryGraphSubsequence_spec (Z := C)
    C.seqSet C.limitSet ((C.hausdorffConverges_iff).mp hC)
    (fun n ↦ (C.seqSetEquiv n).symm.trans ((gs n).trans (C.seqSetEquiv n)))
  let g' := C.limitSetEquiv.trans (g.trans C.limitSetEquiv.symm)
  have he : C.limitSetEquiv.symm.trans (g'.trans C.limitSetEquiv) = g := by
    ext x
    simp [g']
  refine ⟨φ, g', hφ, ?_⟩
  simpa only [seqGraph, limitGraph, he] using hg

end CommonRealization
end PaperN.PartI
