import PaperN.PartI.CommonRealization

namespace PaperN.PartI
open MeasureTheory
universe u

/-- Replace only the probability, retaining the entire compact metric carrier. -/
def MeasuredCompact.withProbability (X : MeasuredCompact.{u}) (μ : ProbabilityMeasure X) :
    MeasuredCompact.{u} where
  Carrier := X
  metric := inferInstance
  compact := inferInstance
  nonempty := inferInstance
  probability := μ

/-- Keep the same embeddings when replacing the sequence's probabilities. -/
def CommonRealization.withProbabilities {Xs : ℕ → MeasuredCompact.{u}} {X : MeasuredCompact.{u}}
    (C : CommonRealization Xs X) (μ : ∀ n, ProbabilityMeasure (Xs n)) :
    CommonRealization (fun n ↦ (Xs n).withProbability (μ n)) X where
  Carrier := C
  metric := inferInstance
  compact := inferInstance
  seqMap := C.seqMap
  limitMap := C.limitMap
  seq_isometry := C.seq_isometry
  limit_isometry := C.limit_isometry
end PaperN.PartI
