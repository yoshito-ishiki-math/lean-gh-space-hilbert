import PaperN.PartI.BallMass
import PaperN.PartI.CompactMinima

namespace PaperN.PartI
open MeasureTheory Set Filter TopologicalSpace
open scoped Topology
universe u

/-- The analytic minimum-ball-mass convergence in a common compact realization. -/
theorem CommonRealization.minimumBallMass_tendsto
    {Xs : ℕ → MeasuredCompact.{u}} {X : MeasuredCompact.{u}}
    (C : CommonRealization Xs X) (hH : C.HausdorffConverges) (hW : C.WeakConverges) (r : ℝ) :
    Tendsto (fun n ↦ minimumBallMass (Xs n).probability r) atTop
      (𝓝 (minimumBallMass X.probability r)) := by
  apply compact_minima_tendsto C.seqSet C.limitSet ((C.hausdorffConverges_iff).mp hH)
    (fun n ↦ ballMass (C.seqProbability n) r) (ballMass C.limitProbability r)
    (continuous_ballMass C.limitProbability r)
    (ballMass_tendstoUniformly C.seqProbability C.limitProbability hW r)
  · intro n
    exact minimumBallMass_range (Xs n).probability (C.seqMap n) (C.seq_isometry n) r
  · exact minimumBallMass_range X.probability C.limitMap C.limit_isometry r

namespace MeasuredGHSpace
/-- Minimum bump mass on the measured-isometry quotient, using the entire carrier. -/
noncomputable def minimumMass (r : ℝ) (q : MeasuredGHSpace.{u}) : ℝ :=
  Quotient.liftOn q (fun X ↦ minimumBallMass X.probability r) (by
    intro X Y h
    obtain ⟨e, he⟩ := h
    exact minimumBallMass_isometryEquiv X.probability Y.probability e he r)

/-- Continuity uses only the already cited metric and common-embedding inputs. -/
theorem continuous_minimumMass (hm : GHPMetricInput.{u}) (hc : GHPCommonEmbeddingInput.{u})
    (r : ℝ) : letI := hm.metricSpace; Continuous (minimumMass r : MeasuredGHSpace.{u} → ℝ) := by
  letI := hm.metricSpace
  apply continuous_iff_seqContinuous.mpr
  intro qs q hq
  let Xs : ℕ → MeasuredCompact.{u} := fun n ↦ (qs n).out
  let X : MeasuredCompact.{u} := q.out
  have ht : Tendsto (fun n ↦ (Xs n).toMeasuredGHSpace) atTop (𝓝 X.toMeasuredGHSpace) := by
    simpa only [Xs, X, MeasuredCompact.toMeasuredGHSpace, Quotient.out_eq] using hq
  obtain ⟨C, hH, hW⟩ := commonMeasuredEmbedding_of_tendsto hm hc Xs X ht
  have hv := C.minimumBallMass_tendsto hH hW r
  have he : ∀ a : MeasuredGHSpace.{u}, minimumBallMass a.out.probability r = minimumMass r a := by
    intro a
    change minimumMass r (Quotient.mk _ a.out) = minimumMass r a
    rw [Quotient.out_eq]
  simpa only [Xs, X, he, Function.comp_def] using hv
end MeasuredGHSpace
end PaperN.PartI
