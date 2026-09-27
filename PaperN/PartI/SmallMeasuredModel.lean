import PaperN.PartI.UniverseAssignment

namespace PaperN.PartI
open MeasureTheory Set GromovHausdorff
universe u v w
local instance modelMeasurable (X : Type*) [TopologicalSpace X] : MeasurableSpace X := borel X
local instance modelBorel (X : Type*) [TopologicalSpace X] : BorelSpace X := ⟨rfl⟩

/-- Whole-carrier measured isometry, also between different universes. -/
structure MeasuredEquiv (X : MeasuredCompact.{u}) (Y : MeasuredCompact.{v}) where
  iso : X ≃ᵢ Y
  map_measure : Measure.map iso X.measure = Y.measure

namespace MeasuredEquiv
noncomputable def refl (X : MeasuredCompact.{u}) : MeasuredEquiv X X :=
  ⟨IsometryEquiv.refl X, Measure.map_id⟩
noncomputable def symm {X : MeasuredCompact.{u}} {Y : MeasuredCompact.{v}}
    (e : MeasuredEquiv X Y) : MeasuredEquiv Y X := ⟨e.iso.symm, by
  rw [← e.map_measure, Measure.map_map e.iso.symm.continuous.measurable e.iso.continuous.measurable]
  convert Measure.map_id (μ := X.measure) using 1
  congr 1
  funext x
  exact e.iso.symm_apply_apply x⟩
noncomputable def trans {X : MeasuredCompact.{u}} {Y : MeasuredCompact.{v}}
    {Z : MeasuredCompact.{w}} (e : MeasuredEquiv X Y) (f : MeasuredEquiv Y Z) : MeasuredEquiv X Z :=
  ⟨e.iso.trans f.iso, by
    change Measure.map (f.iso ∘ e.iso) X.measure = Z.measure
    rw [← Measure.map_map f.iso.continuous.measurable e.iso.continuous.measurable,
      e.map_measure, f.map_measure]⟩
end MeasuredEquiv

/-- A small measured representative, transporting the given measure, not the selected one. -/
noncomputable def smallMeasured (X : MeasuredCompact.{u}) : MeasuredCompact.{0} :=
  (smallCarrier X).withProbability (X.probability.map
    (smallCarrierEquiv X).symm.continuous.measurable.aemeasurable)

noncomputable def smallMeasuredEquiv (X : MeasuredCompact.{u}) : MeasuredEquiv (smallMeasured X) X :=
  ⟨smallCarrierEquiv X, by
    change Measure.map (smallCarrierEquiv X)
      (Measure.map (smallCarrierEquiv X).symm X.measure) = X.measure
    rw [Measure.map_map (smallCarrierEquiv X).continuous.measurable
      (smallCarrierEquiv X).symm.continuous.measurable]
    convert Measure.map_id (μ := X.measure) using 1
    congr 1
    funext x
    exact (smallCarrierEquiv X).apply_symm_apply x⟩

/-- Equality in the small model is exactly whole-carrier measured isometry, at all universes. -/
theorem smallMeasured_class_eq_iff (X : MeasuredCompact.{u}) (Y : MeasuredCompact.{v}) :
    (smallMeasured X).toMeasuredGHSpace = (smallMeasured Y).toMeasuredGHSpace ↔
      Nonempty (MeasuredEquiv X Y) := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := Quotient.exact h
    exact ⟨((smallMeasuredEquiv X).symm.trans ⟨e, he⟩).trans (smallMeasuredEquiv Y)⟩
  · rintro ⟨e⟩
    let f := ((smallMeasuredEquiv X).trans e).trans (smallMeasuredEquiv Y).symm
    exact Quotient.sound ⟨f.iso, f.map_measure⟩

/-- The canonical map from a universe-indexed quotient to the common small model. -/
noncomputable def smallMeasuredClass : MeasuredGHSpace.{u} → MeasuredGHSpace.{0} :=
  Quotient.lift (fun X ↦ (smallMeasured X).toMeasuredGHSpace) (by
    intro X Y h
    obtain ⟨e, he⟩ := h
    exact (smallMeasured_class_eq_iff X Y).mpr ⟨⟨e, he⟩⟩)

theorem smallMeasuredClass_injective : Function.Injective smallMeasuredClass.{u} := by
  intro x y
  induction x using Quotient.inductionOn with | _ X =>
    induction y using Quotient.inductionOn with | _ Y =>
      intro h
      obtain ⟨e⟩ := (smallMeasured_class_eq_iff X Y).mp h
      exact Quotient.sound ⟨e.iso, e.map_measure⟩

noncomputable def uliftIsometry (X : Type u) [MetricSpace X] : ULift.{v} X ≃ᵢ X :=
  { Equiv.ulift with isometry_toFun := fun _ _ ↦ rfl }

noncomputable def liftMeasured (X : MeasuredCompact.{0}) : MeasuredCompact.{u} where
  Carrier := ULift.{u} X
  metric := inferInstance
  compact := inferInstance
  nonempty := inferInstance
  probability := by
    letI : MeasurableSpace (ULift.{u} X) := borel _
    letI : BorelSpace (ULift.{u} X) := ⟨rfl⟩
    exact X.probability.map (uliftIsometry X).symm.continuous.measurable.aemeasurable

noncomputable def liftMeasuredEquiv (X : MeasuredCompact.{0}) : MeasuredEquiv (liftMeasured.{u} X) X := by
  letI : MeasurableSpace (ULift.{u} X) := borel _
  letI : BorelSpace (ULift.{u} X) := ⟨rfl⟩
  refine ⟨uliftIsometry X, ?_⟩

  change Measure.map (uliftIsometry X) (Measure.map (uliftIsometry X).symm X.measure) = X.measure
  rw [Measure.map_map (uliftIsometry X).continuous.measurable
    (uliftIsometry X).symm.continuous.measurable]
  convert Measure.map_id (μ := X.measure) using 1
  congr 1

theorem smallMeasuredClass_surjective : Function.Surjective smallMeasuredClass.{u} := by
  intro q
  induction q using Quotient.inductionOn with | _ X =>
    refine ⟨(liftMeasured.{u} X).toMeasuredGHSpace, ?_⟩
    let e := (smallMeasuredEquiv (liftMeasured.{u} X)).trans (liftMeasuredEquiv X)
    exact Quotient.sound ⟨e.iso, e.map_measure⟩

noncomputable def measuredUniverseEquiv : MeasuredGHSpace.{u} ≃ MeasuredGHSpace.{0} :=
  Equiv.ofBijective smallMeasuredClass ⟨smallMeasuredClass_injective, smallMeasuredClass_surjective⟩
end PaperN.PartI
