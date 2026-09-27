import PaperN.PartI.InvariantAssignment

namespace PaperN.PartI
open MeasureTheory GromovHausdorff Filter
open scoped Topology

/-- A small whole-carrier representative of each GH class; its seed probability is immaterial. -/
noncomputable def ghRepresentative (q : GHSpace) : MeasuredCompact.{0} :=
  (invariantProjectionSurjectivity_spec q).choose

theorem ghRepresentative_class (q : GHSpace) : toGHSpace (ghRepresentative q) = q :=
  (invariantProjectionSurjectivity_spec q).choose_spec.2

/-- The selected measured class, initially defined using the chosen carrier representative. -/
noncomputable def selectedGHSection (hm : GHPMetricInput.{0})
    (hs : InvariantFiberLawSelectionStatement hm) (q : GHSpace) : MeasuredGHSpace.{0} :=
  ((ghRepresentative q).withProbability (selectedProbability hm hs (ghRepresentative q))).toMeasuredGHSpace

/-- The section agrees with the manuscript formula on every entire compact carrier. -/
theorem selectedGHSection_class (hm : GHPMetricInput.{0})
    (hs : InvariantFiberLawSelectionStatement hm) (X : MeasuredCompact.{0}) :
    selectedGHSection hm hs (toGHSpace X) =
      (X.withProbability (selectedProbability hm hs X)).toMeasuredGHSpace := by
  obtain ⟨e⟩ := toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp (ghRepresentative_class (toGHSpace X))
  exact Quotient.sound ⟨e, congrArg ProbabilityMeasure.toMeasure
    (selectedProbability_natural hm hs _ X e)⟩

theorem forget_selectedGHSection (hm : GHPMetricInput.{0})
    (hs : InvariantFiberLawSelectionStatement hm) (q : GHSpace) :
    (selectedGHSection hm hs q).forget = q := ghRepresentative_class q

theorem selectedGHSection_invariant (hm : GHPMetricInput.{0})
    (hs : InvariantFiberLawSelectionStatement hm) (q : GHSpace) :
    (selectedGHSection hm hs q).invariantFullSupport :=
  selectedProbability_fullSupport_invariant hm hs (ghRepresentative q)

/-- M3 and the cited ordinary common-embedding theorem prove continuity in the GHP metric. -/
theorem continuous_selectedGHSection (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hg : GHCommonEmbeddingInput.{0}) (hs : InvariantFiberLawSelectionStatement hm) :
    letI := hm.metricSpace
    Continuous (selectedGHSection hm hs) := by
  letI := hm.metricSpace
  apply continuous_iff_seqContinuous.mpr
  intro qs q hq
  let Xs := fun n ↦ ghRepresentative (qs n)
  let X := ghRepresentative q
  have hx : Tendsto (fun n ↦ toGHSpace (Xs n)) atTop (𝓝 (toGHSpace X)) := by
    simpa only [Xs, X, ghRepresentative_class] using hq
  obtain ⟨C, hH⟩ := hg Xs X hx
  let D : CommonRealization
      (fun n ↦ (Xs n).withProbability (selectedProbability hm hs (Xs n)))
      (X.withProbability (selectedProbability hm hs X)) := {
    Carrier := C
    metric := inferInstance
    compact := inferInstance
    seqMap := C.seqMap
    limitMap := C.limitMap
    seq_isometry := C.seq_isometry
    limit_isometry := C.limit_isometry }
  have hW : D.WeakConverges := selectedProbability_tendsto hm hp hs Xs X C hH
  exact tendsto_iff_dist_tendsto_zero.mpr (D.ghpDist_tendsto hH hW)
end PaperN.PartI
