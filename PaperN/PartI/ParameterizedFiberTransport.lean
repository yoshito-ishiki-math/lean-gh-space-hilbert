import PaperN.PartI.VaryingFiberTransport
import PaperN.PartI.FiberLawAverage

set_option backward.isDefEq.respectTransparency false

namespace PaperN.PartI
open MeasureTheory Filter Set TopologicalSpace Metric GromovHausdorff
open scoped Topology
universe u v

/-- The joint domain of fiber transport for a family of entire compact carriers. -/
abbrev FamilyFiber {T : Type v} (Xs : T → MeasuredCompact.{u}) :=
  {p : T × InvariantMeasuredGHSpace.{u} // p.2.val.forget = toGHSpace (Xs p.1)}

/-- The joint fiber domain is closed whenever the carrier classes vary continuously. -/
theorem isClosed_familyFiber (hm : GHPMetricInput.{u})
    {T : Type v} [TopologicalSpace T] (Xs : T → MeasuredCompact.{u})
    (hX : Continuous (fun t ↦ toGHSpace (Xs t))) :
    letI := hm.metricSpace
    letI := hm.invariantMetricSpace
    IsClosed {p : T × InvariantMeasuredGHSpace.{u} | p.2.val.forget = toGHSpace (Xs p.1)} := by
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  exact isClosed_eq (((ghpForgetLipschitz_spec hm).continuous.comp continuous_subtype_val).comp
    continuous_snd) (hX.comp continuous_fst)

/-- Joint fiber transport into a fixed ambient space, before any averaging. -/
noncomputable def familyFiberProbability
    {T : Type v} (Xs : T → MeasuredCompact.{u})
    {Z : Type u} [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (e : ∀ t, Xs t → Z) (he : ∀ t, Isometry (e t))
    (p : FamilyFiber Xs) : ProbabilityMeasure Z :=
  (fiberProbability (Xs p.val.1) ⟨p.val.2, p.property⟩).map
    (e p.val.1)

/-- The same prescribed Hausdorff convergence makes the carrier classes continuous in GH. -/
theorem continuous_familyGH
    {T : Type v} [MetricSpace T] (Xs : T → MeasuredCompact.{u})
    {Z : Type u} [MetricSpace Z] [CompactSpace Z]
    (e : ∀ t, Xs t → Z) (he : ∀ t, Isometry (e t))
    (hH : ∀ (ts : ℕ → T) (t : T), Tendsto ts atTop (𝓝 t) →
      Tendsto (fun n ↦ hausdorffDist (range (e (ts n))) (range (e t))) atTop (𝓝 0)) :
    Continuous (fun t ↦ toGHSpace (Xs t)) := by
  apply continuous_iff_seqContinuous.mpr
  intro ts t ht
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun n ↦ dist_nonneg)
    (fun n ↦ ghDist_le_hausdorffDist (he (ts n)) (he t)) (hH ts t ht)

/-- Joint continuity follows from the varying-carrier result, including nonisolated parameters.
The Hausdorff hypothesis is the sequential continuity of the prescribed carrier images. -/
theorem continuous_familyFiberProbability (hm : GHPMetricInput.{u})
    {T : Type v} [MetricSpace T] (Xs : T → MeasuredCompact.{u})
    {Z : Type u} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (e : ∀ t, Xs t → Z) (he : ∀ t, Isometry (e t))
    (hH : ∀ (ts : ℕ → T) (t : T), Tendsto ts atTop (𝓝 t) →
      Tendsto (fun n ↦ hausdorffDist (range (e (ts n))) (range (e t))) atTop (𝓝 0)) :
    letI := hm.metricSpace
    letI := hm.invariantMetricSpace
    Continuous (familyFiberProbability Xs e he) := by
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  cases BorelSpace.measurable_eq (α := Z)
  apply continuous_iff_seqContinuous.mpr
  intro ps p hp
  have ht : Tendsto (fun n ↦ (ps n).val.1) atTop (𝓝 p.val.1) :=
    (continuous_fst.comp continuous_subtype_val).continuousAt.tendsto.comp hp
  have hq : Tendsto (fun n ↦ (ps n).val.2.val) atTop (𝓝 p.val.2.val) :=
    (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).continuousAt.tendsto.comp hp
  let C : CommonRealization (fun n ↦ Xs (ps n).val.1) (Xs p.val.1) := {
    Carrier := Z
    metric := inferInstance
    compact := inferInstance
    seqMap := fun n ↦ e (ps n).val.1
    limitMap := e p.val.1
    seq_isometry := fun n ↦ he (ps n).val.1
    limit_isometry := he p.val.1 }
  have h := varying_fiberProbability_tendsto hm _ _ C (hH _ _ ht)
    (fun n ↦ ⟨(ps n).val.2, (ps n).property⟩) ⟨p.val.2, p.property⟩ hq
  exact h
end PaperN.PartI
