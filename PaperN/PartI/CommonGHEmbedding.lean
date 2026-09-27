import PaperN.PartI.UniverseGHP
import PaperN.PartI.CommonGHEmbeddingStatements

namespace PaperN.PartI
open MeasureTheory Set Metric Filter GromovHausdorff
open scoped Topology
universe u

/-- The same cited small input applies to arbitrarily large carriers. -/
theorem ghCommonEmbedding_universe (hg : GHCommonEmbeddingInput.{0}) :
    GHCommonEmbeddingInput.{u} := by
  intro Xs X h
  have hx (Y : MeasuredCompact.{u}) : toGHSpace (smallMeasured Y) = toGHSpace Y :=
    toGHSpace_eq_toGHSpace_iff_isometryEquiv.mpr ⟨(smallMeasuredEquiv Y).iso⟩
  have h' : Tendsto (fun n ↦ toGHSpace (smallMeasured (Xs n))) atTop
      (𝓝 (toGHSpace (smallMeasured X))) := by simpa only [hx] using h
  obtain ⟨C, hC⟩ := hg (fun n ↦ smallMeasured (Xs n)) (smallMeasured X) h'
  let E := uliftIsometry.{0,u} C
  let D : CommonRealization Xs X := {
    Carrier := ULift.{u} C
    metric := inferInstance
    compact := inferInstance
    seqMap := fun n ↦ E.symm ∘ C.seqMap n ∘ (smallMeasuredEquiv (Xs n)).iso.symm
    limitMap := E.symm ∘ C.limitMap ∘ (smallMeasuredEquiv X).iso.symm
    seq_isometry := fun n ↦ E.symm.isometry.comp
      ((C.seq_isometry n).comp (smallMeasuredEquiv (Xs n)).iso.symm.isometry)
    limit_isometry := E.symm.isometry.comp
      (C.limit_isometry.comp (smallMeasuredEquiv X).iso.symm.isometry) }
  refine ⟨D, ?_⟩
  change Tendsto (fun n ↦ hausdorffDist _ _) atTop (𝓝 0)
  simpa only [CommonRealization.HausdorffConverges, D, Set.range_comp, (smallMeasuredEquiv _).iso.symm.surjective.range_eq,
    Set.image_univ, hausdorffDist_image E.symm.isometry] using hC

theorem commonGHCauchyEmbedding_spec (hg : GHCommonEmbeddingInput.{0}) :
    CommonGHCauchyEmbeddingStatement.{u} := by
  intro Xs h
  obtain ⟨q, hq⟩ := cauchySeq_tendsto_of_complete h
  let X := liftMeasured.{u} (ghRepresentative q)
  have hx : toGHSpace X = q :=
    (toGHSpace_eq_toGHSpace_iff_isometryEquiv.mpr ⟨(liftMeasuredEquiv _).iso⟩).trans
      (ghRepresentative_class q)
  have h' : Tendsto (fun n ↦ toGHSpace (Xs n)) atTop (𝓝 (toGHSpace X)) := by rwa [hx]
  obtain ⟨C, hC⟩ := ghCommonEmbedding_universe hg Xs X h'
  exact ⟨X, C, hC, h'⟩
end PaperN.PartI
