import PaperN.PartI.InvariantGDeltaStatements
import PaperN.PartI.CommonIsometryLimits
import PaperN.PartI.FullSupportGDelta

namespace PaperN.PartI
open MeasureTheory Set Filter TopologicalSpace
open scoped Topology
universe u

/-- Defect measured in a common ambient space is the intrinsic defect. -/
theorem isometryDefect_embedding (X : MeasuredCompact.{u})
    {Z : Type*} [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (e : X → Z) (he : Isometry e) (g : X ≃ᵢ X) :
    levyProkhorovDist (Measure.map e X.measure) (Measure.map (e ∘ g) X.measure) =
      X.isometryDefect g := by
  rw [← Measure.map_map he.continuous.measurable g.continuous.measurable,
    levyProkhorovDist_map_isometry e he]
  rfl

/-- Intrinsic Prokhorov defects converge along the extracted isometry subsequence. -/
theorem CommonRealization.isometryDefect_subsequence
    {Xs : ℕ → MeasuredCompact.{u}} {X : MeasuredCompact.{u}}
    (C : CommonRealization Xs X) (hH : C.HausdorffConverges) (hW : C.WeakConverges)
    (gs : ∀ n, Xs n ≃ᵢ Xs n) :
    ∃ (φ : ℕ → ℕ) (g : X ≃ᵢ X), StrictMono φ ∧
      Tendsto (fun n ↦ (Xs (φ n)).isometryDefect (gs (φ n))) atTop (𝓝 (X.isometryDefect g)) := by
  obtain ⟨φ, g, hφ, hA⟩ := C.actionProbability_subsequence hH hW gs
  refine ⟨φ, g, hφ, ?_⟩
  have hd := levyProkhorovDist_tendsto (hW.comp hφ.tendsto_atTop) hA
  have hs : ∀ n, levyProkhorovDist (C.seqProbability n : Measure C)
      (C.seqActionProbability gs n : Measure C) = (Xs n).isometryDefect (gs n) :=
    fun n ↦ isometryDefect_embedding (Xs n) (C.seqMap n) (C.seq_isometry n) (gs n)
  have hl : levyProkhorovDist (C.limitProbability : Measure C)
      (C.limitActionProbability g : Measure C) = X.isometryDefect g :=
    isometryDefect_embedding X C.limitMap C.limit_isometry g
  simpa only [Function.comp_def, hs, hl] using hd

/-- A fixed lower bound on a witnessed defect survives GHP convergence. -/
theorem hasIsometryDefect_of_tendsto (hm : GHPMetricInput.{u}) (hc : GHPCommonEmbeddingInput.{u})
    (Xs : ℕ → MeasuredCompact.{u}) (X : MeasuredCompact.{u}) (r : ℝ)
    (hs : ∀ n, (Xs n).HasIsometryDefect r) : letI := hm.metricSpace
    Tendsto (fun n ↦ (Xs n).toMeasuredGHSpace) atTop (𝓝 X.toMeasuredGHSpace) →
      X.HasIsometryDefect r := by
  letI := hm.metricSpace
  intro hconv
  obtain ⟨C, hH, hW⟩ := commonMeasuredEmbedding_of_tendsto hm hc Xs X hconv
  choose gs hgs using hs
  obtain ⟨φ, g, _, hg⟩ := C.isometryDefect_subsequence hH hW gs
  exact ⟨g, ge_of_tendsto hg (Filter.Eventually.of_forall fun n ↦ hgs (φ n))⟩

namespace MeasuredGHSpace
lemma hasIsometryDefect_out (q : MeasuredGHSpace.{u}) (r : ℝ) :
    q.out.HasIsometryDefect r ↔ q.hasIsometryDefect r := by
  change hasIsometryDefect r (Quotient.mk _ q.out) ↔ hasIsometryDefect r q
  rw [Quotient.out_eq]

/-- The closed exceptional set used in the manuscript, for every real threshold. -/
theorem isClosed_hasIsometryDefect (hm : GHPMetricInput.{u}) (hc : GHPCommonEmbeddingInput.{u})
    (r : ℝ) : letI := hm.metricSpace
    IsClosed {q : MeasuredGHSpace.{u} | q.hasIsometryDefect r} := by
  letI := hm.metricSpace
  apply isSeqClosed_iff_isClosed.mp
  intro qs q hqs hq
  apply (hasIsometryDefect_out q r).mp
  apply hasIsometryDefect_of_tendsto hm hc (fun n ↦ (qs n).out) q.out r
    (fun n ↦ (hasIsometryDefect_out (qs n) r).mpr (hqs n))
  simpa only [MeasuredCompact.toMeasuredGHSpace, Quotient.out_eq] using hq

/-- No dyadic defect witnesses is exactly invariance under every carrier isometry. -/
theorem invariant_iff_no_dyadic_defect (q : MeasuredGHSpace.{u}) :
    q.invariant ↔ ∀ n : ℕ, ¬ q.hasIsometryDefect ((1 / 2 : ℝ) ^ n) := by
  refine Quotient.inductionOn q ?_
  intro X
  exact X.invariant_iff_no_dyadic_defect

theorem invariant_eq_iInter :
    {q : MeasuredGHSpace.{u} | q.invariant} =
      ⋂ n : ℕ, {q | q.hasIsometryDefect ((1 / 2 : ℝ) ^ n)}ᶜ := by
  ext q
  simp only [mem_setOf_eq, mem_iInter, mem_compl_iff]
  exact invariant_iff_no_dyadic_defect q
end MeasuredGHSpace

/-- The entire varying-space invariance Gδ lemma, with the existing explicit inputs. -/
theorem invariantGDelta_spec (hm : GHPMetricInput.{u}) (hc : GHPCommonEmbeddingInput.{u}) :
    InvariantGDeltaStatement hm := by
  letI := hm.metricSpace
  change IsGδ {q : MeasuredGHSpace.{u} | q.invariant}
  rw [MeasuredGHSpace.invariant_eq_iInter]
  exact IsGδ.iInter_of_isOpen fun n ↦ (MeasuredGHSpace.isClosed_hasIsometryDefect hm hc _).isOpen_compl
/-- The newly separated quotient predicates agree with the original combined predicate. -/
theorem MeasuredGHSpace.invariantFullSupport_iff (q : MeasuredGHSpace.{u}) :
    q.invariantFullSupport ↔ q.fullSupport ∧ q.invariant := by
  refine Quotient.inductionOn q ?_
  intro X
  rfl

/-- Both varying-space conditions define the original invariant-full-support Gδ subset. -/
theorem invariantFullSupportGDelta_spec (hm : GHPMetricInput.{u}) (hc : GHPCommonEmbeddingInput.{u}) :
    InvariantFullSupportGDeltaStatement hm := by
  letI := hm.metricSpace
  have he : {q : MeasuredGHSpace.{u} | q.invariantFullSupport} =
      {q | q.fullSupport} ∩ {q | q.invariant} := by
    ext q
    exact q.invariantFullSupport_iff
  change IsGδ {q : MeasuredGHSpace.{u} | q.invariantFullSupport}
  rw [he]
  exact (fullSupportGDelta_spec hm hc).inter (invariantGDelta_spec hm hc)
end PaperN.PartI
