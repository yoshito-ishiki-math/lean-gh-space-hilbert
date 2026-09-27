import PaperN.PartI.Remeasure
import PaperN.PartI.GHPExternalStatements
import PaperN.PartI.FixedProbability

namespace PaperN.PartI
open MeasureTheory Set GromovHausdorff
universe u

/-- Invariant probabilities on a fixed entire carrier; full support is not imposed here. -/
abbrev InvariantProbability (X : MeasuredCompact.{u}) :=
  {μ : ProbabilityMeasure X // ∀ g : X ≃ᵢ X, Measure.map g (μ : Measure X) = (μ : Measure X)}

/-- The actual fiber over the isometry class of the fixed carrier. -/
abbrev InvariantFiber (X : MeasuredCompact.{u}) :=
  {q : InvariantMeasuredGHSpace.{u} // q.val.forget = toGHSpace X}

/-- On invariant probabilities the measured-isometry quotient loses no information. -/
theorem probability_eq_of_invariant_class_eq (X : MeasuredCompact.{u})
    (μ ν : ProbabilityMeasure X)
    (hi : ∀ g : X ≃ᵢ X, Measure.map g (μ : Measure X) = (μ : Measure X))
    (h : (X.withProbability μ).toMeasuredGHSpace = (X.withProbability ν).toMeasuredGHSpace) :
    μ = ν := by
  obtain ⟨e, he⟩ := Quotient.exact h
  apply ProbabilityMeasure.toMeasure_injective
  exact (hi e).symm.trans he

/-- Changing carrier by any isometry represents the same measured class. -/
theorem probability_map_class {X Y : MeasuredCompact.{u}} (e : X ≃ᵢ Y)
    (μ : ProbabilityMeasure X) :
    (Y.withProbability (μ.map e)).toMeasuredGHSpace =
      (X.withProbability μ).toMeasuredGHSpace := by
  symm
  exact Quotient.sound ⟨e, rfl⟩

/-- Every invariant fiber point has a full-support invariant realization on the specified carrier. -/
theorem exists_fiberProbability (X : MeasuredCompact.{u}) (q : InvariantFiber X) :
    ∃ μ : ProbabilityMeasure X,
      (X.withProbability μ).InvariantFullSupport ∧
      (X.withProbability μ).toMeasuredGHSpace = q.val.val := by
  let Y := q.val.val.out
  have hrep : Y.toMeasuredGHSpace = q.val.val := Quotient.out_eq _
  have hY : Y.InvariantFullSupport := by
    have h := q.val.property
    rw [← hrep] at h
    exact h
  have hcarrier : toGHSpace Y = toGHSpace X := by
    change Y.toMeasuredGHSpace.forget = toGHSpace X
    rw [hrep]
    exact q.property
  obtain ⟨e⟩ := toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp hcarrier
  let μ := Y.probability.map e
  have hiso : Y.Isomorphic (X.withProbability μ) := ⟨e, rfl⟩
  exact ⟨μ, MeasuredCompact.invariantFullSupport_of_isomorphic hiso hY,
    (Quotient.sound hiso).symm.trans hrep⟩

/-- The canonical probability on a fixed carrier represented by an invariant fiber point. -/
noncomputable def fiberProbability (X : MeasuredCompact.{u}) (q : InvariantFiber X) :
    ProbabilityMeasure X := (exists_fiberProbability X q).choose

theorem fiberProbability_fullSupport_invariant (X : MeasuredCompact.{u}) (q : InvariantFiber X) :
    (X.withProbability (fiberProbability X q)).InvariantFullSupport :=
  (exists_fiberProbability X q).choose_spec.1

theorem fiberProbability_class (X : MeasuredCompact.{u}) (q : InvariantFiber X) :
    (X.withProbability (fiberProbability X q)).toMeasuredGHSpace = q.val.val :=
  (exists_fiberProbability X q).choose_spec.2

/-- Uniqueness removes all choices of representative and identifying isometry. -/
theorem fiberProbability_unique (X : MeasuredCompact.{u}) (q : InvariantFiber X)
    (μ : ProbabilityMeasure X) (hμ : (X.withProbability μ).toMeasuredGHSpace = q.val.val) :
    fiberProbability X q = μ :=
  probability_eq_of_invariant_class_eq X _ _ (fiberProbability_fullSupport_invariant X q).2
    ((fiberProbability_class X q).trans hμ.symm)

/-- In particular, transport from every representative and every isometry gives the same result. -/
theorem fiberProbability_eq_map (X Y : MeasuredCompact.{u}) (q : InvariantFiber X)
    (hY : Y.toMeasuredGHSpace = q.val.val) (e : Y ≃ᵢ X) :
    fiberProbability X q = Y.probability.map e := by
  apply fiberProbability_unique
  exact (probability_map_class e Y.probability).trans hY

/-- Naturality at each fiber point, before averaging any law. -/
theorem fiberProbability_natural {X Y : MeasuredCompact.{u}} (e : X ≃ᵢ Y)
    (qx : InvariantFiber X) (qy : InvariantFiber Y) (hq : qx.val = qy.val) :
    fiberProbability Y qy =
      (fiberProbability X qx).map e := by
  apply fiberProbability_unique
  exact (probability_map_class e _).trans ((fiberProbability_class X qx).trans
    (congrArg Subtype.val hq))
end PaperN.PartI
