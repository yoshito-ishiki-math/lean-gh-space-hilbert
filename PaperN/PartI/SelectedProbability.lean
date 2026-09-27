import PaperN.PartI.SelectedProbabilityStatements
import PaperN.PartI.FiberNaturality
import PaperN.PartI.InvariantSelection

namespace PaperN.PartI
open MeasureTheory Set GromovHausdorff

/-- Use the selected continuous fiber law, restrict it, transport it, and take its barycenter. -/
noncomputable def selectedProbability (hm : GHPMetricInput.{0})
    (hs : InvariantFiberLawSelectionStatement hm) (X : MeasuredCompact.{0}) : ProbabilityMeasure X := by
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{0} := borel _
  letI : MeasurableSpace GHSpace := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{0} := ⟨rfl⟩
  letI : BorelSpace GHSpace := ⟨rfl⟩
  exact averageConcentratedLaw hm X (hs.choose (toGHSpace X)) (hs.choose_spec (toGHSpace X)).2.1

theorem selectedProbability_fullSupport_invariant (hm : GHPMetricInput.{0})
    (hs : InvariantFiberLawSelectionStatement hm) (X : MeasuredCompact.{0}) :
    (X.withProbability (selectedProbability hm hs X)).InvariantFullSupport := by
  exact averageConcentratedLaw_fullSupport_invariant hm X _ _

/-- The constructed average is natural under every isometry between whole carriers. -/
theorem selectedProbability_natural (hm : GHPMetricInput.{0})
    (hs : InvariantFiberLawSelectionStatement hm) (X Y : MeasuredCompact.{0}) (e : X ≃ᵢ Y) :
    (selectedProbability hm hs X).map e =
      selectedProbability hm hs Y := by
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{0} := borel _
  letI : MeasurableSpace GHSpace := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{0} := ⟨rfl⟩
  letI : BorelSpace GHSpace := ⟨rfl⟩
  have hGH : toGHSpace X = toGHSpace Y := toGHSpace_eq_toGHSpace_iff_isometryEquiv.mpr ⟨e⟩
  have hy : (hs.choose (toGHSpace X) : Measure InvariantMeasuredGHSpace)
      {q | q.val.forget = toGHSpace Y} = 1 := by
    rw [hGH]
    exact (hs.choose_spec (toGHSpace Y)).2.1
  have h := averageConcentratedLaw_natural hm e (hs.choose (toGHSpace X))
    (hs.choose_spec (toGHSpace X)).2.1 hy
  unfold selectedProbability
  convert h using 1
  congr 1
  exact congrArg hs.choose hGH.symm

/-- The seed probability in `MeasuredCompact` does not affect the selected measure. -/
theorem selectedProbability_withProbability (hm : GHPMetricInput.{0})
    (hs : InvariantFiberLawSelectionStatement hm) (X : MeasuredCompact.{0})
    (ν : ProbabilityMeasure X) :
    selectedProbability hm hs (X.withProbability ν) = selectedProbability hm hs X := by
  have h := selectedProbability_natural hm hs X (X.withProbability ν) (IsometryEquiv.refl X)
  apply ProbabilityMeasure.toMeasure_injective
  have he := congrArg ProbabilityMeasure.toMeasure h
  change Measure.map id (selectedProbability hm hs X : Measure X) = _ at he
  rw [Measure.map_id] at he
  exact he.symm

/-- M1 and M2 for the actual Valov/barycenter construction; InvariantAssignment adds M3. -/
theorem naturalInvariantAssignment_spec (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hc : GHPCommonEmbeddingInput.{0}) (hg : GHCommonEmbeddingInput.{0})
    (ha : ProbabilityApproximationInput.{0}) (hv : InvariantValovInput hm hp hc) :
    NaturalInvariantAssignmentStatement := by
  let hs := invariantFiberLawSelection_spec hm hp hc hg ha hv
  exact ⟨selectedProbability hm hs, selectedProbability_fullSupport_invariant hm hs,
    selectedProbability_natural hm hs⟩
end PaperN.PartI
