import PaperN.PartI.GHPDefinitions

/-! Common-ambient data and the exact metric-convergence conclusion of Khezeli Lemma 2.5. -/
namespace PaperN.PartI
open MeasureTheory Set Metric Filter
open scoped Topology
universe u

/-- A single compact space receiving a sequence of entire carriers and its limit. -/
structure CommonRealization (Xs : ℕ → MeasuredCompact.{u}) (X : MeasuredCompact.{u}) where
  Carrier : Type u
  metric : MetricSpace Carrier
  compact : @CompactSpace Carrier metric.toUniformSpace.toTopologicalSpace
  seqMap : ∀ n, Xs n → Carrier
  limitMap : X → Carrier
  seq_isometry : ∀ n, Isometry (seqMap n)
  limit_isometry : Isometry limitMap

instance {Xs : ℕ → MeasuredCompact.{u}} {X : MeasuredCompact.{u}} :
    CoeSort (CommonRealization Xs X) (Type u) := ⟨CommonRealization.Carrier⟩
attribute [instance] CommonRealization.metric CommonRealization.compact
instance {Xs : ℕ → MeasuredCompact.{u}} {X : MeasuredCompact.{u}}
    (C : CommonRealization Xs X) : MeasurableSpace C := borel C
instance {Xs : ℕ → MeasuredCompact.{u}} {X : MeasuredCompact.{u}}
    (C : CommonRealization Xs X) : BorelSpace C := ⟨rfl⟩

namespace CommonRealization
variable {Xs : ℕ → MeasuredCompact.{u}} {X : MeasuredCompact.{u}}
noncomputable def seqProbability (C : CommonRealization Xs X) (n : ℕ) : ProbabilityMeasure C :=
  ProbabilityMeasure.map (Xs n).probability (C.seqMap n)
noncomputable def limitProbability (C : CommonRealization Xs X) : ProbabilityMeasure C :=
  ProbabilityMeasure.map X.probability C.limitMap

def HausdorffConverges (C : CommonRealization Xs X) : Prop :=
  Tendsto (fun n ↦ hausdorffDist (range (C.seqMap n)) (range C.limitMap)) atTop (𝓝 0)

def ProkhorovConverges (C : CommonRealization Xs X) : Prop :=
  Tendsto (fun n ↦ levyProkhorovDist (C.seqProbability n : Measure C)
    (C.limitProbability : Measure C)) atTop (𝓝 0)

def WeakConverges (C : CommonRealization Xs X) : Prop :=
  Tendsto C.seqProbability atTop (𝓝 C.limitProbability)
end CommonRealization

/-- Forward direction of Khezeli Lemma 2.5 for Example 2.1(iii), with Prokhorov
convergence rather than the manuscript's final weak-convergence formulation. -/
def GHPCommonEmbeddingInput : Prop :=
  ∀ (Xs : ℕ → MeasuredCompact.{u}) (X : MeasuredCompact.{u}),
    Tendsto (fun n ↦ ghpDist (Xs n) X) atTop (𝓝 0) →
      ∃ C : CommonRealization Xs X, C.HausdorffConverges ∧ C.ProkhorovConverges

/-- The manuscript's complete common-measured-embedding conclusion. -/
def CommonMeasuredEmbeddingStatement : Prop :=
  ∀ (Xs : ℕ → MeasuredCompact.{u}) (X : MeasuredCompact.{u}),
    Tendsto (fun n ↦ ghpDist (Xs n) X) atTop (𝓝 0) →
      ∃ C : CommonRealization Xs X, C.HausdorffConverges ∧ C.WeakConverges
end PaperN.PartI
