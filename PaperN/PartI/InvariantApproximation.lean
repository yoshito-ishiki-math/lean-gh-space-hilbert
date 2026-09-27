import PaperN.PartI.InvariantApproximationStatements
import PaperN.PartI.MixtureConvergence
import PaperN.PartI.HaarConvergence
import PaperN.PartI.CommonGHPConvergence

namespace PaperN.PartI
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped NNReal Topology
universe u
namespace CommonRealization
variable {Xs : ℕ → MeasuredCompact.{u}} {X : MeasuredCompact.{u}}

/-- Concrete full-support perturbation followed by Haar averaging. -/
theorem invariantApproximation_spec (C : CommonRealization Xs X) :
    C.InvariantApproximationStatement := by
  intro hH hW hi
  let t : ℕ → ℝ≥0 := fun n ↦ (1 / 2) ^ (n + 1)
  have ht : ∀ n, t n ≤ 1 := fun n ↦ pow_le_one₀ (by positivity) (by norm_num)
  have htpos : ∀ n, 0 < t n := fun n ↦ pow_pos (by norm_num) _
  have htzero : Tendsto (fun n ↦ (t n : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (1 / 2)
    simpa [t, pow_succ] using h
  let μ (n : ℕ) := probabilityMixture (Xs n).probability
    (fullSupportProbability (X := Xs n)) (t n) (ht n)
  have hμ (n : ℕ) : IsOpenPosMeasure (μ n : Measure (Xs n)) := by
    letI : IsOpenPosMeasure (fullSupportProbability (X := Xs n) : Measure (Xs n)) :=
      denseAtomicMeasure_fullSupport
    exact probabilityMixture_fullSupport _ _ _ _ (htpos n)
  let D := C.withProbabilities μ
  have hDW : D.WeakConverges := C.mixture_weakConverges hW _ t ht htzero
  have hDH : D.HausdorffConverges := hH
  let ν (n : ℕ) := haarAverage (μ n)
  have hν (n : ℕ) : ((Xs n).withProbability (ν n)).InvariantFullSupport := by
    letI := hμ n
    letI := haarAverage_fullSupport (μ n)
    change (haarAverage (μ n) : Measure (Xs n)).support = univ ∧ _
    exact ⟨Measure.support_eq_univ, haarAverage_invariant (μ n)⟩
  have hνW : (C.withProbabilities ν).WeakConverges :=
    D.haarConvergence_spec hDH hDW hi
  exact ⟨ν, hν, hνW, (C.withProbabilities ν).ghpDist_tendsto hH hνW⟩
end CommonRealization
end PaperN.PartI
