import PaperN.PartII.MeasureKernelConvergence
import PaperN.PartI.InvariantAssignment

namespace PaperN.PartII.AmbientKernel
open MeasureTheory Filter PaperN.PartI
open scoped Topology

variable (hm : GHPMetricInput.{0}) (hs : InvariantFiberLawSelectionStatement hm)
variable {Xs : ℕ → MeasuredCompact.{0}} {X : MeasuredCompact.{0}}
variable (C : CommonRealization Xs X)

noncomputable def selectedSequenceOperator (n : ℕ) : C(C, ℂ) →L[ℂ] C(C, ℂ) :=
  ambientOperator ⟨C.seqMap n, (C.seq_isometry n).continuous⟩
    (selectedProbability hm hs (Xs n) : Measure (Xs n))

noncomputable def selectedLimitOperator : C(C, ℂ) →L[ℂ] C(C, ℂ) :=
  ambientOperator ⟨C.limitMap, C.limit_isometry.continuous⟩
    (selectedProbability hm hs X : Measure X)

theorem selectedSequenceOperator_strong (hp : GHPPolishInput hm)
    (hH : C.HausdorffConverges) (f : C(C, ℂ)) :
    Tendsto (fun n ↦ selectedSequenceOperator hm hs C n f) atTop
      (𝓝 (selectedLimitOperator hm hs C f)) := by
  exact ambientOperator_strong_of_pushforward
    (fun n ↦ ⟨C.seqMap n, (C.seq_isometry n).continuous⟩)
    (fun n ↦ selectedProbability hm hs (Xs n))
    ⟨C.limitMap, C.limit_isometry.continuous⟩ (selectedProbability hm hs X)
    (selectedProbability_tendsto hm hp hs Xs X C hH) f

theorem selectedSequenceOperator_collectivelyCompact :
    ∃ K : Set C(C, ℂ), IsCompact K ∧
      ∀ n (f : C(C, ℂ)), ‖f‖ ≤ 1 → selectedSequenceOperator hm hs C n f ∈ K :=
  ambientOperator_collectivelyCompact
    (fun n ↦ ⟨C.seqMap n, (C.seq_isometry n).continuous⟩)
    (fun n ↦ selectedProbability hm hs (Xs n))

theorem selectedSequenceOperator_differences_collectivelyCompact :
    ∃ K : Set C(C, ℂ), IsCompact K ∧
      ∀ n (f : C(C, ℂ)), ‖f‖ ≤ 1 →
        selectedSequenceOperator hm hs C n f - selectedLimitOperator hm hs C f ∈ K := by
  obtain ⟨K, hK, hmem⟩ := measureOperator_differences_collectivelyCompact (Z := C)
  refine ⟨K, hK, ?_⟩
  intro n f hf
  unfold selectedSequenceOperator selectedLimitOperator
  rw [ambientOperator_eq_measureOperator, ambientOperator_eq_measureOperator]
  exact hmem _ _ f hf

theorem selectedLimitOperator_compact : IsCompactOperator (selectedLimitOperator hm hs C) :=
  ambientOperator_compact ⟨C.limitMap, C.limit_isometry.continuous⟩
    (selectedProbability hm hs X : Measure X)

end PaperN.PartII.AmbientKernel
