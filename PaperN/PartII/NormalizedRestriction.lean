import PaperN.PartII.GramRestriction

namespace PaperN.PartII
open MeasureTheory
open scoped BigOperators
variable {X Z ι : Type*} [MetricSpace X] [MetricSpace Z] [CompactSpace Z]
variable [MeasurableSpace Z] [BorelSpace Z] [Fintype ι] [DecidableEq ι]

omit [CompactSpace Z] [BorelSpace Z] in
theorem normalize_restrict_mem (e : C(X, Z)) (μ : ProbabilityMeasure Z)
    (g : ι → C(Z, ℝ)) (S : Submodule ℝ C(X, ℝ)) (hg : ∀ i, (g i).comp e ∈ S) (i : ι) :
    (normalizeContinuousFamily μ g i).comp e ∈ S := by
  have he : (normalizeContinuousFamily μ g i).comp e =
      ∑ j, gramNormalizer (continuousGram μ g) j i • (g j).comp e := by
    ext x
    simp [normalizeContinuousFamily, transformContinuousBasis]
  rw [he]
  exact S.sum_mem fun j _ ↦ S.smul_mem _ (hg j)

end PaperN.PartII
