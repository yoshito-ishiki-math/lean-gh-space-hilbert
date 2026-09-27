import PaperN.PartI.CommonRealization
import PaperN.PartI.CommonAmbient
import PaperN.PartI.GHPDistance

namespace PaperN.PartI
open MeasureTheory Set Metric Filter
open scoped Topology
universe u
namespace CommonRealization
variable {Xs : ℕ → MeasuredCompact.{u}} {X : MeasuredCompact.{u}}

/-- A common realization supplies an admissible coupling at each index. -/
def couplingAt (C : CommonRealization Xs X) (n : ℕ) : CompactCoupling (Xs n) X where
  Carrier := C
  metric := inferInstance
  compact := inferInstance
  left := C.seqMap n
  right := C.limitMap
  left_isometry := C.seq_isometry n
  right_isometry := C.limit_isometry

theorem ghpDist_le_max (C : CommonRealization Xs X) (n : ℕ) :
    ghpDist (Xs n) X ≤ max (hausdorffDist (range (C.seqMap n)) (range C.limitMap))
      (levyProkhorovDist (C.seqProbability n : Measure C) (C.limitProbability : Measure C)) := by
  have h := ENNReal.toReal_mono (C.couplingAt n).cost_ne_top
    (ghpEDist_le_cost (C.couplingAt n))
  have he := ENNReal.toReal_max
    (ne_top_of_le_ne_top (C.couplingAt n).cost_ne_top (le_max_left _ _))
    (levyProkhorovEDist_ne_top (C.couplingAt n).leftMeasure (C.couplingAt n).rightMeasure)
  exact h.trans_eq he

/-- The reverse common-embedding implication is proved directly from the GHP infimum. -/
theorem ghpDist_tendsto (C : CommonRealization Xs X)
    (hH : C.HausdorffConverges) (hW : C.WeakConverges) :
    Tendsto (fun n ↦ ghpDist (Xs n) X) atTop (𝓝 0) := by
  have hP := (weak_tendsto_iff_prokhorov C.seqProbability C.limitProbability).mp hW
  have hmax := hH.max hP
  simp only [max_self] at hmax
  exact squeeze_zero (fun n ↦ ENNReal.toReal_nonneg) C.ghpDist_le_max hmax
end CommonRealization
end PaperN.PartI
