import PaperN.PartII.CoordinatePullback
import PaperN.PartII.ObjectiveTransport
import PaperN.PartII.LpNormTransport

namespace PaperN.PartII
open MeasureTheory
variable {X Y ι : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [MetricSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [Fintype ι]

/-- Under an isometric pushforward, the selected coefficient at an image point
is exactly the source coefficient for the restricted family. -/
theorem coordinateLpMinimizer_map_isometry
    (μ : ProbabilityMeasure X) [(μ : Measure X).IsOpenPosMeasure]
    (e : X → Y) (he : Isometry e) (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [StrictConvexSpace ℝ (Lp ℝ p (μ : Measure X))]
    (v : ι → C(Y, ℝ))
    (hv : LinearIndependent ℝ (fun i ↦ (v i).comp ⟨e, he.continuous⟩)) (x : X) :
    coordinateLpMinimizer (μ.map he.continuous.measurable.aemeasurable : Measure Y) p v
      (ContinuousMap.toLp p (μ.map he.continuous.measurable.aemeasurable : Measure Y) ℝ
        (distanceProfile (e x))) =
    coordinateLpMinimizer (μ : Measure X) p (fun i ↦ (v i).comp ⟨e, he.continuous⟩)
      (ContinuousMap.toLp p (μ : Measure X) ℝ (distanceProfile x)) := by
  apply mapped_distanceObjective_minimizer_eq μ e he p hp v hv x
  exact fun b ↦ coordinateLpMinimizer_objective_minimal
    (μ.map he.continuous.measurable.aemeasurable) p hp v (e x) b

/-- Exact equality of pairs under isometric carrier pullback with matching measures. -/
theorem bestApproximationCoordinatePair_comap
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    [(μ : Measure X).IsOpenPosMeasure] [(ν : Measure Y).IsOpenPosMeasure]
    (e : X → Y) (he : Isometry e) (hμ : μ.map he.continuous.measurable.aemeasurable = ν)
    (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [StrictConvexSpace ℝ (Lp ℝ p (μ : Measure X))]
    [StrictConvexSpace ℝ (Lp ℝ p (ν : Measure Y))]
    (v : ι → C(Y, ℝ)) (hv : LinearIndependent ℝ v)
    (hve : LinearIndependent ℝ (fun i ↦ (v i).comp ⟨e, he.continuous⟩)) :
    (bestApproximationCoordinatePair (ν : Measure Y) p v hv).comap ⟨e, he.continuous⟩ =
      bestApproximationCoordinatePair (μ : Measure X) p
        (fun i ↦ (v i).comp ⟨e, he.continuous⟩) hve := by
  have hc : ((bestApproximationCoordinatePair (ν : Measure Y) p v hv).comap
      ⟨e, he.continuous⟩).coordinates =
      (bestApproximationCoordinatePair (μ : Measure X) p
        (fun i ↦ (v i).comp ⟨e, he.continuous⟩) hve).coordinates := by
    apply ContinuousMap.ext
    intro x
    have h := coordinateLpMinimizer_map_isometry μ e he p hp v hve x
    rw [hμ] at h
    exact h
  have hn : ((bestApproximationCoordinatePair (ν : Measure Y) p v hv).comap
      ⟨e, he.continuous⟩).norm =
      (bestApproximationCoordinatePair (μ : Measure X) p
        (fun i ↦ (v i).comp ⟨e, he.continuous⟩) hve).norm := by
    ext b
    have h := coordinateLpNorm_map μ (⟨e, he.continuous⟩ : C(X, Y)) p hp v b
    rw [hμ] at h
    exact h
  generalize (bestApproximationCoordinatePair (ν : Measure Y) p v hv).comap
    ⟨e, he.continuous⟩ = a at hc hn ⊢
  generalize bestApproximationCoordinatePair (μ : Measure X) p
    (fun i ↦ (v i).comp ⟨e, he.continuous⟩) hve = b at hc hn ⊢
  cases a
  cases b
  cases hc
  cases hn
  rfl

end PaperN.PartII
