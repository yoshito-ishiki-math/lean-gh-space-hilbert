import PaperN.PartI.GHPCompleteness
import PaperN.PartI.OrdinaryProbabilityLifting
import PaperN.PartI.FiberTopology
import PaperN.PartI.GHSection
import Mathlib.Topology.Sequences

namespace PaperN.PartI
open Filter Set GromovHausdorff MeasureTheory TopologicalSpace
open scoped Topology

/-- Probabilities on a GH-dense carrier family are dense in measured GH space. -/
theorem denseRange_probabilityClasses (Xs : ℕ → MeasuredCompact.{0})
    (hXs : DenseRange (fun n ↦ toGHSpace (Xs n))) :
    letI := ghpMetricInput_proved.metricSpace
    DenseRange (fun p : Σ n, ProbabilityMeasure (Xs n) ↦
      ((Xs p.1).withProbability p.2).toMeasuredGHSpace) := by
  letI := ghpMetricInput_proved.metricSpace
  intro q
  obtain ⟨X, rfl⟩ := Quotient.exists_rep q
  obtain ⟨ys, hys, hy⟩ := mem_closure_iff_seq_limit.mp (hXs (toGHSpace X))
  choose ns hns using hys
  have hh : Tendsto (fun n ↦ toGHSpace (Xs (ns n))) atTop (𝓝 (toGHSpace X)) := by
    simpa only [hns] using hy
  obtain ⟨μ, hμ⟩ := exists_probability_classes_tendsto (fun n ↦ Xs (ns n)) X hh
  exact mem_closure_of_tendsto hμ (Filter.Eventually.of_forall fun n ↦
    ⟨⟨ns n, μ n⟩, rfl⟩)

/-- Separability of the exact small-carrier GHP metric. -/
theorem ghp_separableSpace :
    letI := ghpMetricInput_proved.metricSpace
    SeparableSpace MeasuredGHSpace.{0} := by
  letI := ghpMetricInput_proved.metricSpace
  obtain ⟨qs, hqs⟩ := exists_dense_seq GHSpace
  let Xs := fun n ↦ ghRepresentative (qs n)
  have hd : DenseRange (fun n ↦ toGHSpace (Xs n)) := by
    simpa only [Xs, ghRepresentative_class] using hqs
  apply (denseRange_probabilityClasses Xs hd).separableSpace
  apply continuous_sigma
  intro n
  exact continuous_probabilityClass ghpMetricInput_proved (Xs n)

/-- Both Polish metric properties are now constructed internally. -/
theorem ghpPolishInput_proved : GHPPolishInput ghpMetricInput_proved.{0} :=
  ⟨ghp_completeSpace, ghp_separableSpace⟩
end PaperN.PartI
