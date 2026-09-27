import PaperN.PartI.OpenProjectionStatements
import PaperN.PartI.InvariantLifts
import PaperN.PartI.GHPExternal

namespace PaperN.PartI
open MeasureTheory Set Filter GromovHausdorff
open scoped Topology

/-- Openness follows from lifting every convergent sequence through each point of its limit fiber. -/
theorem isOpenMap_of_sequence_lifts {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [SequentialSpace B] (f : A → B)
    (hlift : ∀ (ys : ℕ → B) (x : A), Tendsto ys atTop (𝓝 (f x)) →
      ∃ xs : ℕ → A, Tendsto xs atTop (𝓝 x) ∧ ∀ n, f (xs n) = ys n) : IsOpenMap f := by
  intro U hU
  apply isClosed_compl_iff.mp
  apply IsSeqClosed.isClosed
  intro ys y hys hy
  rintro ⟨x, hx, rfl⟩
  obtain ⟨xs, hxs, he⟩ := hlift ys x hy
  have hev := hxs.eventually (hU.mem_nhds hx)
  obtain ⟨n, hn⟩ := hev.exists
  exact hys n ⟨xs n, hn, he n⟩

/-- Representative-level invariant lifts give lifts in the actual invariant GHP subtype. -/
theorem invariantProjection_sequenceLift (hm : GHPMetricInput.{0})
    (hg : GHCommonEmbeddingInput.{0}) (ha : ProbabilityApproximationInput.{0}) :
    letI := hm.metricSpace
    letI := hm.invariantMetricSpace
    ∀ (ys : ℕ → GHSpace) (x : InvariantMeasuredGHSpace.{0}),
      Tendsto ys atTop (𝓝 x.val.forget) →
      ∃ xs : ℕ → InvariantMeasuredGHSpace.{0}, Tendsto xs atTop (𝓝 x) ∧
        ∀ n, (xs n).val.forget = ys n := by
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  intro ys x hconv
  let X := x.val.out
  have hrep : X.toMeasuredGHSpace = x.val := Quotient.out_eq _
  have hX : X.InvariantFullSupport := by
    have hx := x.property
    rw [← hrep] at hx
    exact hx
  let M (n : ℕ) : MeasuredCompact :=
    letI : MeasurableSpace (ys n).Rep := borel (ys n).Rep
    letI : BorelSpace (ys n).Rep := ⟨rfl⟩
    ⟨(ys n).Rep, inferInstance, inferInstance, inferInstance, fullSupportProbability⟩
  have hM (n : ℕ) : toGHSpace (M n) = ys n := (ys n).toGHSpace_rep
  have hforget : toGHSpace X = x.val.forget := by
    change X.toMeasuredGHSpace.forget = x.val.forget
    rw [hrep]
  obtain ⟨ν, hν, hνconv⟩ := invariantLifts_spec hm hg ha M X hX
    (by simpa only [hM, hforget] using hconv)
  let xs (n : ℕ) : InvariantMeasuredGHSpace :=
    ⟨((M n).withProbability (ν n)).toMeasuredGHSpace, hν n⟩
  refine ⟨xs, ?_, fun n ↦ hM n⟩
  apply tendsto_subtype_rng.mpr
  simpa only [hrep] using hνconv

/-- The whole continuous open surjection proposition; openness is proved, not an input. -/
theorem openInvariantProjection_spec (hm : GHPMetricInput.{0})
    (hg : GHCommonEmbeddingInput.{0}) (ha : ProbabilityApproximationInput.{0}) :
    OpenInvariantProjectionStatement hm := by
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  obtain ⟨hcont, hsurj⟩ := invariantProjectionContinuousSurjective_spec hm
  exact ⟨hcont, isOpenMap_of_sequence_lifts _ (invariantProjection_sequenceLift hm hg ha), hsurj⟩
end PaperN.PartI
