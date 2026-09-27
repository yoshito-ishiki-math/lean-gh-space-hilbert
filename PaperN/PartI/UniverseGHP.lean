import PaperN.PartI.SmallMeasuredModel
import PaperN.PartI.ProkhorovIsometry

namespace PaperN.PartI
open MeasureTheory Set Metric
universe u v
local instance universeGHPMeasurable (X : Type*) [TopologicalSpace X] : MeasurableSpace X := borel X
local instance universeGHPBorel (X : Type*) [TopologicalSpace X] : BorelSpace X := ⟨rfl⟩

/-- Any nonempty compact ambient has an isometric copy in every target universe. -/
noncomputable def resizedAmbientEquiv (Z : Type u) [MetricSpace Z] [CompactSpace Z] [Nonempty Z] :
    Z ≃ᵢ ULift.{v} (smallCarrier Z) :=
  (smallCarrierEquiv Z).symm.trans (uliftIsometry (smallCarrier Z)).symm

namespace CompactCoupling
variable {X Y : MeasuredCompact.{u}} {A B : MeasuredCompact.{v}}
noncomputable def resize (C : CompactCoupling X Y) (ex : MeasuredEquiv A X)
    (ey : MeasuredEquiv B Y) : CompactCoupling A B := by
  letI : Nonempty C := ⟨C.left (Classical.choice inferInstance)⟩
  let e := resizedAmbientEquiv.{u,v} C
  exact {
    Carrier := ULift.{v} (smallCarrier C)
    metric := inferInstance
    compact := inferInstance
    left := e ∘ C.left ∘ ex.iso
    right := e ∘ C.right ∘ ey.iso
    left_isometry := e.isometry.comp (C.left_isometry.comp ex.iso.isometry)
    right_isometry := e.isometry.comp (C.right_isometry.comp ey.iso.isometry) }

theorem cost_resize (C : CompactCoupling X Y) (ex : MeasuredEquiv A X)
    (ey : MeasuredEquiv B Y) : (C.resize ex ey).cost = C.cost := by
  letI : Nonempty C := ⟨C.left (Classical.choice inferInstance)⟩
  let e := resizedAmbientEquiv.{u,v} C
  letI : MeasurableSpace (ULift.{v} (smallCarrier C)) := borel _
  letI : BorelSpace (ULift.{v} (smallCarrier C)) := ⟨rfl⟩
  have hr (f : X → C) : range (e ∘ f ∘ ex.iso) = e '' range f := by
    rw [range_comp, ex.iso.surjective.range_comp]
  have hs (f : Y → C) : range (e ∘ f ∘ ey.iso) = e '' range f := by
    rw [range_comp, ey.iso.surjective.range_comp]
  change max (hausdorffEDist (range (e ∘ C.left ∘ ex.iso)) (range (e ∘ C.right ∘ ey.iso)))
    (levyProkhorovEDist (Measure.map (e ∘ C.left ∘ ex.iso) A.measure)
      (Measure.map (e ∘ C.right ∘ ey.iso) B.measure)) = C.cost
  rw [hr, hs, hausdorffEDist_image e.isometry,
    ← Measure.map_map e.continuous.measurable (C.left_isometry.comp ex.iso.isometry).continuous.measurable,
    ← Measure.map_map e.continuous.measurable (C.right_isometry.comp ey.iso.isometry).continuous.measurable,
    ← Measure.map_map C.left_isometry.continuous.measurable ex.iso.continuous.measurable,
    ← Measure.map_map C.right_isometry.continuous.measurable ey.iso.continuous.measurable,
    ex.map_measure, ey.map_measure, levyProkhorovEDist_map_isometry e e.isometry]
  rfl
end CompactCoupling

/-- The max-infimum GHP distance is independent of universe, without a metric axiom input. -/
theorem ghpEDist_measuredEquiv {X Y : MeasuredCompact.{u}} {A B : MeasuredCompact.{v}}
    (ex : MeasuredEquiv A X) (ey : MeasuredEquiv B Y) : ghpEDist A B = ghpEDist X Y := by
  apply le_antisymm
  · apply le_iInf
    intro C
    exact (ghpEDist_le_cost (C.resize ex ey)).trans_eq (C.cost_resize ex ey)
  · apply le_iInf
    intro C
    exact (ghpEDist_le_cost (C.resize ex.symm ey.symm)).trans_eq (C.cost_resize ex.symm ey.symm)

theorem smallMeasured_ghpDist (X Y : MeasuredCompact.{u}) :
    ghpDist (smallMeasured X) (smallMeasured Y) = ghpDist X Y :=
  congrArg ENNReal.toReal (ghpEDist_measuredEquiv (smallMeasuredEquiv X) (smallMeasuredEquiv Y))

theorem smallMeasuredClass_distance (x y : MeasuredGHSpace.{u}) :
    MeasuredGHSpace.distance (smallMeasuredClass x) (smallMeasuredClass y) =
      MeasuredGHSpace.distance x y := by
  induction x using Quotient.inductionOn with | _ X =>
    induction y using Quotient.inductionOn with | _ Y =>
      exact smallMeasured_ghpDist X Y
/-- Transfer the two cited metric laws from the small model, rather than assuming them again. -/
theorem GHPMetricInput.universe (hm : GHPMetricInput.{0}) : GHPMetricInput.{u} := {
  triangle x y z := by
    rw [← smallMeasuredClass_distance x z, ← smallMeasuredClass_distance x y,
      ← smallMeasuredClass_distance y z]
    exact hm.triangle _ _ _
  separated x y h := smallMeasuredClass_injective (hm.separated _ _
    ((smallMeasuredClass_distance x y).trans h)) }

noncomputable def measuredUniverseIsometry (hm : GHPMetricInput.{0}) :
    letI := hm.metricSpace
    letI := (GHPMetricInput.universe.{u} hm).metricSpace
    MeasuredGHSpace.{u} ≃ᵢ MeasuredGHSpace.{0} := by
  letI := hm.metricSpace
  letI := (GHPMetricInput.universe.{u} hm).metricSpace
  exact { measuredUniverseEquiv with
    isometry_toFun := Isometry.of_dist_eq smallMeasuredClass_distance }
/-- Completeness and separability are inherited by the exact GHP metric in every universe. -/
theorem ghpPolish_universe (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm) :
    GHPPolishStatement (GHPMetricInput.universe.{u} hm) := by
  letI := hm.metricSpace
  letI := (GHPMetricInput.universe.{u} hm).metricSpace
  letI := hp.complete
  letI := hp.separable
  let E := measuredUniverseIsometry.{u} hm
  letI := E.completeSpace
  letI := E.symm.surjective.denseRange.separableSpace E.symm.continuous
  exact ⟨inferInstance, inferInstance, inferInstance⟩
end PaperN.PartI
