import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.MetricSpace.Isometry

/-! Whole-carrier measured compact spaces. No quotient by measure support is used. -/
namespace PaperN.PartI
open MeasureTheory Set
universe u

/-- A carrier together with its metric, compactness, and a Borel probability. -/
structure MeasuredCompact where
  Carrier : Type u
  metric : MetricSpace Carrier
  compact : @CompactSpace Carrier metric.toUniformSpace.toTopologicalSpace
  nonempty : Nonempty Carrier
  probability : @ProbabilityMeasure Carrier (borel Carrier)

instance : CoeSort MeasuredCompact (Type u) := ⟨MeasuredCompact.Carrier⟩
attribute [instance] MeasuredCompact.metric MeasuredCompact.compact MeasuredCompact.nonempty
instance (X : MeasuredCompact) : MeasurableSpace X := borel X
instance (X : MeasuredCompact) : BorelSpace X := ⟨rfl⟩

namespace MeasuredCompact
/-- The probability is on the entire carrier, even if its support is smaller. -/
noncomputable def measure (X : MeasuredCompact) : Measure X := X.probability
instance (X : MeasuredCompact) : IsProbabilityMeasure X.measure := X.probability.prop

/-- Whole-carrier measure-preserving isometry. -/
def Isomorphic (X Y : MeasuredCompact.{u}) : Prop :=
  ∃ e : X ≃ᵢ Y, Measure.map e X.measure = Y.measure

lemma isomorphic_refl (X : MeasuredCompact) : Isomorphic X X := by
  exact ⟨IsometryEquiv.refl X, Measure.map_id⟩

lemma isomorphic_symm {X Y : MeasuredCompact} (h : Isomorphic X Y) : Isomorphic Y X := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, ?_⟩
  rw [← he, Measure.map_map e.symm.continuous.measurable e.continuous.measurable]
  convert Measure.map_id (μ := X.measure) using 1
  congr 1
  funext x
  exact e.symm_apply_apply x

lemma isomorphic_trans {X Y Z : MeasuredCompact} (h : Isomorphic X Y)
    (k : Isomorphic Y Z) : Isomorphic X Z := by
  obtain ⟨e, he⟩ := h
  obtain ⟨f, hf⟩ := k
  refine ⟨e.trans f, ?_⟩
  change Measure.map (f ∘ e) X.measure = Z.measure
  rw [← Measure.map_map f.continuous.measurable e.continuous.measurable, he, hf]

instance measuredSetoid : Setoid MeasuredCompact.{u} where
  r := Isomorphic
  iseqv := ⟨isomorphic_refl, isomorphic_symm, isomorphic_trans⟩

/-- The full carrier participates in both conjuncts. -/
def InvariantFullSupport (X : MeasuredCompact) : Prop :=
  X.measure.support = univ ∧ ∀ g : X ≃ᵢ X, Measure.map g X.measure = X.measure
end MeasuredCompact

/-- Universe-indexed isomorphism classes; a small Polish model is a later step. -/
def MeasuredGHSpace := Quotient MeasuredCompact.measuredSetoid.{u}

end PaperN.PartI
