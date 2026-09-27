import PaperN.PartII.CoordinateLpNorm
import Mathlib.Analysis.Convex.StrictConvexSpace

namespace PaperN.PartII
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Finite-dimensional linear subspaces admit best approximations. -/
theorem exists_bestApproximation (S : Submodule ℝ F) [FiniteDimensional ℝ S] (x : F) :
    ∃ a : S, ∀ b : S, ‖x - a‖ ≤ ‖x - b‖ := by
  have hne : (Metric.closedBall (0 : S) (2 * ‖x‖)).Nonempty :=
    ⟨0, by simp [norm_nonneg]⟩
  obtain ⟨a, ha, hmin⟩ := (isCompact_closedBall (0 : S) (2 * ‖x‖)).exists_isMinOn hne
    ((continuous_const.sub S.subtypeL.continuous).norm.continuousOn)
  refine ⟨a, fun b ↦ ?_⟩
  by_cases hb : b ∈ Metric.closedBall (0 : S) (2 * ‖x‖)
  · exact hmin hb
  · have ha0 := hmin (show (0 : S) ∈ Metric.closedBall (0 : S) (2 * ‖x‖) by
      simp [norm_nonneg])
    have hb' : 2 * ‖x‖ < ‖(b : F)‖ := by
      have hnb : ¬ ‖b‖ ≤ 2 * ‖x‖ := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hb
      exact lt_of_not_ge hnb
    have ht : ‖(b : F)‖ ≤ ‖x‖ + ‖x - b‖ := by
      calc
        ‖(b : F)‖ = ‖x - (x - b)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖x‖ + ‖x - b‖ := norm_sub_le _ _
    change ‖x - (a : F)‖ ≤ ‖x - (0 : F)‖ at ha0
    rw [sub_zero] at ha0
    linarith

/-- Strict convexity makes best approximations in linear subspaces unique. -/
theorem bestApproximation_unique [StrictConvexSpace ℝ F] (S : Submodule ℝ F)
    (x : F) (a b : S)
    (ha : ∀ c : S, ‖x - a‖ ≤ ‖x - c‖)
    (hb : ∀ c : S, ‖x - b‖ ≤ ‖x - c‖) : a = b := by
  by_contra hab
  have hn : ‖x - (a : F)‖ = ‖x - (b : F)‖ := le_antisymm (ha b) (hb a)
  have hne : x - (a : F) ≠ x - (b : F) := by
    intro h
    exact hab (Subtype.ext (sub_right_injective h))
  have ht := (norm_midpoint_lt_iff hn).mpr hne
  have hm := ha ((1 / 2 : ℝ) • (a + b))
  have he : (1 / 2 : ℝ) • ((x - (a : F)) + (x - (b : F))) =
      x - ((1 / 2 : ℝ) • ((a : F) + (b : F))) := by module
  rw [he] at ht
  exact (not_lt_of_ge hm) ht

end PaperN.PartII

namespace PaperN.PartII
open MeasureTheory
variable {X ι : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Fintype ι]
  (μ : Measure X) [IsFiniteMeasure μ] (p : ENNReal) [Fact (1 ≤ p)]

theorem exists_coordinateLp_minimizer (v : ι → C(X, ℝ)) (f : Lp ℝ p μ) :
    ∃ a : EuclideanSpace ℝ ι, ∀ b : EuclideanSpace ℝ ι,
      ‖f - coordinateLpMap μ p v a‖ ≤ ‖f - coordinateLpMap μ p v b‖ := by
  obtain ⟨a, ha⟩ := exists_bestApproximation (LinearMap.range (coordinateLpMap μ p v)) f
  obtain ⟨c, hc⟩ := a.property
  refine ⟨c, fun b ↦ ?_⟩
  have h := ha ⟨coordinateLpMap μ p v b, ⟨b, rfl⟩⟩
  simpa only [hc] using h

theorem coordinateLp_minimizer_unique [μ.IsOpenPosMeasure] [StrictConvexSpace ℝ (Lp ℝ p μ)]
    (v : ι → C(X, ℝ)) (hv : LinearIndependent ℝ v) (f : Lp ℝ p μ)
    (a b : EuclideanSpace ℝ ι)
    (ha : ∀ c, ‖f - coordinateLpMap μ p v a‖ ≤ ‖f - coordinateLpMap μ p v c‖)
    (hb : ∀ c, ‖f - coordinateLpMap μ p v b‖ ≤ ‖f - coordinateLpMap μ p v c‖) : a = b := by
  let T := coordinateLpMap μ p v
  have hi : Function.Injective T :=
    (ContinuousMap.toLp_injective μ).comp (coordinateSynthesis_injective v hv)
  apply hi
  have h := bestApproximation_unique (LinearMap.range T) f
    ⟨T a, ⟨a, rfl⟩⟩ ⟨T b, ⟨b, rfl⟩⟩
    (fun c ↦ by obtain ⟨d, hd⟩ := c.property; simpa only [← hd] using ha d)
    (fun c ↦ by obtain ⟨d, hd⟩ := c.property; simpa only [← hd] using hb d)
  exact congrArg Subtype.val h

/-- A chosen best coefficient vector. Uniqueness is proved separately. -/
noncomputable def coordinateLpMinimizer (v : ι → C(X, ℝ)) (f : Lp ℝ p μ) :
    EuclideanSpace ℝ ι := (exists_coordinateLp_minimizer μ p v f).choose

theorem coordinateLpMinimizer_spec (v : ι → C(X, ℝ)) (f : Lp ℝ p μ)
    (b : EuclideanSpace ℝ ι) :
    ‖f - coordinateLpMap μ p v (coordinateLpMinimizer μ p v f)‖ ≤
      ‖f - coordinateLpMap μ p v b‖ :=
  (exists_coordinateLp_minimizer μ p v f).choose_spec b

end PaperN.PartII

namespace PaperN.PartII
open MeasureTheory Metric Set
variable {X ι : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Fintype ι]
  (μ : Measure X) [IsProbabilityMeasure μ] (p : ENNReal) [Fact (1 ≤ p)]

theorem coordinateLpMinimizer_norm_le_two_diam (v : ι → C(X, ℝ)) (x : X) :
    coordinateLpNorm μ p v
      (coordinateLpMinimizer μ p v (ContinuousMap.toLp p μ ℝ (distanceProfile x))) ≤
        2 * diam (univ : Set X) := by
  apply coordinateLpNorm_le_two_diam μ p v x
  simpa only [map_zero, sub_zero] using
    coordinateLpMinimizer_spec μ p v (ContinuousMap.toLp p μ ℝ (distanceProfile x)) 0

end PaperN.PartII
