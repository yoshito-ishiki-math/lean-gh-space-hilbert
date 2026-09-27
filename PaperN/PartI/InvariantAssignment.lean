import PaperN.PartI.InvariantAssignmentStatements
import PaperN.PartI.SequenceFiberAverage
import PaperN.PartI.SelectedProbability

namespace PaperN.PartI
open MeasureTheory Filter GromovHausdorff
open scoped Topology

/-- M3 for the same Valov/barycenter selection already used for M1 and M2. -/
theorem selectedProbability_tendsto (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm)
    (Xs : ℕ → MeasuredCompact.{0}) (X : MeasuredCompact.{0})
    (C : CommonRealization Xs X) (hH : C.HausdorffConverges) :
    Tendsto (fun n ↦ (selectedProbability hm hs (Xs n)).map
      (C.seq_isometry n).continuous.measurable.aemeasurable) atTop
      (𝓝 ((selectedProbability hm hs X).map C.limit_isometry.continuous.measurable.aemeasurable)) := by
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{0} := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{0} := ⟨rfl⟩
  letI : MeasurableSpace GHSpace := borel _
  letI : BorelSpace GHSpace := ⟨rfl⟩
  have hGH : Tendsto (fun n ↦ toGHSpace (Xs n)) atTop (𝓝 (toGHSpace X)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun n ↦ dist_nonneg)
      (fun n ↦ ghDist_le_hausdorffDist (C.seq_isometry n) C.limit_isometry) hH
  exact averageConcentratedLaw_tendsto hm hp Xs X C hH
    (fun n ↦ hs.choose (toGHSpace (Xs n))) (hs.choose (toGHSpace X))
    (fun n ↦ (hs.choose_spec (toGHSpace (Xs n))).2.1) (hs.choose_spec (toGHSpace X)).2.1
    (hs.choose.continuous.continuousAt.tendsto.comp hGH)

/-- The same concrete assignment satisfies M1, M2 and M3, conditional on the six existing
cited inputs. This does not supply inhabitants of those external inputs. -/
theorem invariantAssignment_spec (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hc : GHPCommonEmbeddingInput.{0}) (hg : GHCommonEmbeddingInput.{0})
    (ha : ProbabilityApproximationInput.{0}) (hv : InvariantValovInput hm hp hc) :
    InvariantAssignmentStatement := by
  let hs := invariantFiberLawSelection_spec hm hp hc hg ha hv
  exact ⟨selectedProbability hm hs, selectedProbability_fullSupport_invariant hm hs,
    selectedProbability_natural hm hs, selectedProbability_tendsto hm hp hs⟩
end PaperN.PartI
