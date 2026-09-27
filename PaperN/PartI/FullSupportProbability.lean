import PaperN.PartI.Definitions
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace PaperN.PartI
open MeasureTheory MeasureTheory.Measure Set TopologicalSpace
open scoped ENNReal
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [Nonempty X]

/-- The dense atomic probability used in lem:invariant-full-support. -/
noncomputable def denseAtomicMeasure : Measure X :=
  Measure.sum (fun n : ℕ ↦ (2 : ℝ≥0∞) ^ (-1 - n : ℤ) • Measure.dirac (denseSeq X n))

instance denseAtomicMeasure_probability : IsProbabilityMeasure (denseAtomicMeasure (X := X)) := by
  constructor
  simp only [denseAtomicMeasure, Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
  exact ENNReal.tsum_two_zpow_neg_add_one

instance denseAtomicMeasure_fullSupport : IsOpenPosMeasure (denseAtomicMeasure (X := X)) := by
  constructor
  intro U hU hne
  obtain ⟨n, hx⟩ := (denseRange_denseSeq X).exists_mem_open hU hne
  have hle := Measure.le_sum (fun n : ℕ ↦
    (2 : ℝ≥0∞) ^ (-1 - n : ℤ) • Measure.dirac (denseSeq X n)) n U
  have hw : (0 : ℝ≥0∞) < (2 : ℝ≥0∞) ^ (-1 - n : ℤ) := ENNReal.zpow_pos (by norm_num) (by simp) _
  have hpos : 0 < denseAtomicMeasure (X := X) U := by
    apply hw.trans_le
    simpa only [denseAtomicMeasure, Measure.smul_apply, Measure.dirac_apply_of_mem hx,
      smul_eq_mul, mul_one] using hle
  exact hpos.ne'

noncomputable def fullSupportProbability : ProbabilityMeasure X :=
  ⟨denseAtomicMeasure, inferInstance⟩

omit [BorelSpace X] in
lemma fullSupportProbability_support :
    (fullSupportProbability (X := X) : Measure X).support = univ := by
  change (denseAtomicMeasure (X := X)).support = univ
  exact Measure.support_eq_univ

end PaperN.PartI
