import PaperN.PartII.PointwiseResolventStability
import PaperN.PartII.CompactResolventBound
import PaperN.PartII.SelectedKernelConvergence
import PaperN.PartII.CircleIntertwining

namespace PaperN.PartII
open Filter
open scoped Topology
universe u

/-- Anselone--Palmer Theorem 5.3(a), specialized to compact subsets of the
limit resolvent. The predicate is retained for compatibility; its inhabitant is proved below. -/
def CollectivelyCompactSpectralInclusionInput : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E),
    (∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x))) →
    (∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Us n x - U x ∈ K) →
    ∀ A : Set ℂ, IsCompact A → A ⊆ resolventSet ℂ U →
      ∀ᶠ n in atTop, A ⊆ resolventSet ℂ (Us n)

/-- Compact resolvent inclusion follows from the internally proved uniform bound. -/
theorem collectivelyCompactSpectralInclusionInput_proved :
    CollectivelyCompactSpectralInclusionInput.{u} := by
  intro E _ _ _ Us U hs hk A hA hr
  obtain ⟨B, hB, hb⟩ := collectivelyCompact_eventually_compact_resolvent_bound
    Us U hs hk A hA hr
  filter_upwards [hb] with n hn
  exact fun z hz ↦ (hn z hz).1

namespace AmbientKernel
open MeasureTheory PaperN.PartI
variable (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
variable (hs : InvariantFiberLawSelectionStatement hm)
variable {Xs : ℕ → MeasuredCompact.{0}} {X : MeasuredCompact.{0}}
variable (C : CommonRealization Xs X)
include hp

theorem selectedSequenceOperator_eventually_resolvent
    (hS : CollectivelyCompactSpectralInclusionInput.{0}) (hH : C.HausdorffConverges)
    (A : Set ℂ) (hA : IsCompact A) (hr : A ⊆ resolventSet ℂ (selectedLimitOperator hm hs C)) :
    ∀ᶠ n in atTop, A ⊆ resolventSet ℂ (selectedSequenceOperator hm hs C n) :=
  hS C(C, ℂ) (selectedSequenceOperator hm hs C) (selectedLimitOperator hm hs C)
    (selectedSequenceOperator_strong hm hs C hp hH)
    (selectedSequenceOperator_differences_collectivelyCompact hm hs C) A hA hr

theorem selectedDistanceOperator_eventually_cutoff_resolvent
    (hH : C.HausdorffConverges)
    (η : ℝ) (hη : 0 < η)
    (hpos : (η : ℂ) ∈ resolventSet ℂ
      (ComplexKernel.distanceOperator (selectedProbability hm hs X : Measure X)))
    (hneg : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ
      (ComplexKernel.distanceOperator (selectedProbability hm hs X : Measure X))) :
    ∀ᶠ n in atTop,
      (η : ℂ) ∈ resolventSet ℂ
        (ComplexKernel.distanceOperator (selectedProbability hm hs (Xs n) : Measure (Xs n))) ∧
      ((-η : ℝ) : ℂ) ∈ resolventSet ℂ
        (ComplexKernel.distanceOperator (selectedProbability hm hs (Xs n) : Measure (Xs n))) := by
  have hne : (η : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hη
  have hnne : ((-η : ℝ) : ℂ) ≠ 0 := by exact_mod_cast neg_ne_zero.mpr (ne_of_gt hη)
  have hp' : (η : ℂ) ∈ resolventSet ℂ (selectedLimitOperator hm hs C) :=
    (nonzero_resolventSet_iff ⟨C.limitMap, C.limit_isometry.continuous⟩ _ C.limit_isometry _ hne).mpr hpos
  have hn' : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (selectedLimitOperator hm hs C) :=
    (nonzero_resolventSet_iff ⟨C.limitMap, C.limit_isometry.continuous⟩ _ C.limit_isometry _ hnne).mpr hneg
  have hev := collectivelyCompact_eventually_finite_resolvent
    (selectedSequenceOperator hm hs C) (selectedLimitOperator hm hs C)
    (selectedSequenceOperator_strong hm hs C hp hH)
    (selectedSequenceOperator_differences_collectivelyCompact hm hs C)
    ({(η : ℂ), ((-η : ℝ) : ℂ)} : Set ℂ) (Set.toFinite _)
    (by intro z hz; rcases Set.mem_insert_iff.mp hz with rfl | hz
        · exact hp'
        · have hz' := Set.mem_singleton_iff.mp hz
          simpa only [hz'] using hn')
  filter_upwards [hev] with n hn
  exact ⟨(nonzero_resolventSet_iff ⟨C.seqMap n, (C.seq_isometry n).continuous⟩ _
    (C.seq_isometry n) _ hne).mp (hn (by simp)),
    (nonzero_resolventSet_iff ⟨C.seqMap n, (C.seq_isometry n).continuous⟩ _
    (C.seq_isometry n) _ hnne).mp (hn (by simp))⟩

end AmbientKernel
end PaperN.PartII
