import PaperN.PartI.CompactRealizationRestriction
import PaperN.PartI.ConvergentCouplings

namespace PaperN.PartI
open Filter Metric MeasureTheory Set
open scoped Topology
universe u

/-- The max-infimum GHP convergence has a compact common measured realization. -/
theorem ghpCommonEmbeddingInput_proved : GHPCommonEmbeddingInput.{u} := by
  intro Ys X h
  have h' : Tendsto (fun n ↦ ghpDist X (Ys n)) atTop (𝓝 0) := by
    simpa only [ghpDist, ghpEDist_comm] using h
  obtain ⟨C, ht⟩ := exists_couplings_cost_tendsto X Ys h'
  let Z := BasedAmbient.CouplingJointCarrier C
  letI : MeasurableSpace Z := borel Z
  letI : BorelSpace Z := ⟨rfl⟩
  apply compactRealization_of_common_ambient Ys X (BasedAmbient.couplingJointBase C)
    (fun n ↦ BasedAmbient.couplingJointMap C n ∘ (C n).right)
    (BasedAmbient.couplingJointBase_isometry C)
    (fun n ↦ (BasedAmbient.couplingJointMap_isometry C n).comp (C n).right_isometry)
  · have hh := squeeze_zero (fun n ↦ ENNReal.toReal_nonneg)
      (fun n ↦ ENNReal.toReal_mono (C n).cost_ne_top (le_max_left _ _)) ht
    change Tendsto (fun n ↦ (Metric.hausdorffEDist (range (C n).left)
      (range (C n).right)).toReal) atTop (𝓝 0) at hh
    convert hh using 1
    funext n
    exact congrArg ENNReal.toReal (BasedAmbient.couplingJoint_hausdorffEDist C n)
  · have hp := squeeze_zero (fun n ↦ ENNReal.toReal_nonneg)
      (fun n ↦ ENNReal.toReal_mono (C n).cost_ne_top (le_max_right _ _)) ht
    change Tendsto (fun n ↦ (levyProkhorovEDist (C n).leftMeasure
      (C n).rightMeasure).toReal) atTop (𝓝 0) at hp
    convert hp using 1
    funext n
    exact congrArg ENNReal.toReal (BasedAmbient.couplingJoint_levyProkhorovEDist C n)
end PaperN.PartI
