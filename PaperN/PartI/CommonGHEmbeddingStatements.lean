import PaperN.PartI.MeasuredProjection
import PaperN.PartI.CommonRealization

namespace PaperN.PartI
open Filter GromovHausdorff
open scoped Topology
universe u

/-- Cauchy version of lem:common-gh-embedding, including an actual nonempty compact limit. -/
def CommonGHCauchyEmbeddingStatement : Prop :=
  ∀ Xs : ℕ → MeasuredCompact.{u}, CauchySeq (fun n ↦ toGHSpace (Xs n)) →
    ∃ (X : MeasuredCompact.{u}) (C : CommonRealization Xs X),
      C.HausdorffConverges ∧ Tendsto (fun n ↦ toGHSpace (Xs n)) atTop (𝓝 (toGHSpace X))

end PaperN.PartI
