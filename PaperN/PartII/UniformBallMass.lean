import PaperN.PartII.DistanceKernel
import Mathlib.MeasureTheory.Measure.OpenPos

namespace PaperN.PartII
open MeasureTheory Metric Set
universe u
variable {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X]
variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
variable [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]

omit [Nonempty X] [BorelSpace X] in
/-- A common positive lower bound for the mass of every ball of a fixed radius. -/
theorem exists_uniform_ball_mass (r : ℝ) (hr : 0 < r) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : X, c ≤ μ.real (ball x r) := by
  classical
  obtain ⟨T,hT,hcover⟩ := Metric.totallyBounded_iff.mp
    (isCompact_univ : IsCompact (univ : Set X)).totallyBounded (r/2) (by positivity)
  have hpos (x : X) : 0 < μ.real (ball x (r/2)) :=
    ENNReal.toReal_pos (ne_of_gt (measure_ball_pos μ x (by positivity))) (measure_ne_top _ _)
  have hmin : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ T, c ≤ μ.real (ball x (r/2)) := by
    clear hcover
    induction T, hT using Set.Finite.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert x T hx hT ih =>
      obtain ⟨c,hc,h⟩ := ih
      refine ⟨min c (μ.real (ball x (r/2))),lt_min hc (hpos x),?_⟩
      intro y hy
      rcases mem_insert_iff.mp hy with rfl | hy
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (h y hy)
  obtain ⟨c,hc,h⟩ := hmin
  refine ⟨c,hc,fun x ↦ ?_⟩
  have hx := hcover (mem_univ x)
  simp only [mem_iUnion,mem_ball] at hx
  obtain ⟨y,hy,hxy⟩ := hx
  apply (h y hy).trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro z hz
  have hz' : dist z y < r/2 := hz
  have ht := dist_triangle z y x
  rw [dist_comm y x] at ht
  change dist z x < r
  linarith

omit [BorelSpace X] in
/-- The infimum used in lem:lp-distance is strictly positive. -/
theorem uniform_ball_mass_pos (r : ℝ) (hr : 0 < r) :
    0 < ⨅ x : X, μ.real (ball x r) := by
  obtain ⟨c,hc,h⟩ := exists_uniform_ball_mass μ r hr
  exact hc.trans_le (le_ciInf h)
end PaperN.PartII
