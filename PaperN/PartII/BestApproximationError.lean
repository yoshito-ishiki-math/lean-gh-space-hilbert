import PaperN.PartII.BestApproximationNaturality
import PaperN.PartII.LpDistance

namespace PaperN.PartII

/-- Pointwise approximation errors control the error between induced distances. -/
theorem norm_sub_error_le {E : Type*} [SeminormedAddCommGroup E] (a b x y : E) :
    |‖a - b‖ - ‖x - y‖| ≤ ‖x - a‖ + ‖y - b‖ := by
  have h := abs_norm_sub_norm_le (a - b) (x - y)
  have he : (a - b) - (x - y) = (a - x) - (b - y) := by abel
  rw [he] at h
  calc
    _ ≤ ‖(a - x) - (b - y)‖ := h
    _ ≤ ‖a - x‖ + ‖b - y‖ := norm_sub_le _ _
    _ = _ := by rw [norm_sub_rev a x, norm_sub_rev b y]

open MeasureTheory
variable {X ι : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Fintype ι]
  (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
  (p : ENNReal) [Fact (1 ≤ p)] [StrictConvexSpace ℝ (Lp ℝ p μ)]

theorem bestApproximation_pseudometric_error_le
    (v : ι → C(X, ℝ)) (hv : LinearIndependent ℝ v)
    (x y : X) (a b : EuclideanSpace ℝ ι) :
    |(bestApproximationCoordinatePair μ p v hv).pseudometric x y - ‖distanceDifferenceLp μ p x y‖| ≤
      ‖ContinuousMap.toLp p μ ℝ (distanceProfile x) - coordinateLpMap μ p v a‖ +
      ‖ContinuousMap.toLp p μ ℝ (distanceProfile y) - coordinateLpMap μ p v b‖ := by
  let fx := ContinuousMap.toLp p μ ℝ (distanceProfile x)
  let fy := ContinuousMap.toLp p μ ℝ (distanceProfile y)
  let ax := coordinateLpMinimizer μ p v fx
  let ay := coordinateLpMinimizer μ p v fy
  change |‖coordinateLpMap μ p v (ax - ay)‖ - ‖distanceDifferenceLp μ p x y‖| ≤ _
  rw [map_sub, distanceDifferenceLp_eq_sub]
  exact (norm_sub_error_le (coordinateLpMap μ p v ax) (coordinateLpMap μ p v ay) fx fy).trans
    (add_le_add (coordinateLpMinimizer_spec μ p v fx a) (coordinateLpMinimizer_spec μ p v fy b))

theorem bestApproximation_pseudometric_dist_error_le
    (v : ι → C(X, ℝ)) (hv : LinearIndependent ℝ v)
    (x y : X) (a b : EuclideanSpace ℝ ι) (ε δ : ℝ)
    (hx : ‖ContinuousMap.toLp p μ ℝ (distanceProfile x) - coordinateLpMap μ p v a‖ ≤ ε)
    (hy : ‖ContinuousMap.toLp p μ ℝ (distanceProfile y) - coordinateLpMap μ p v b‖ ≤ ε)
    (hd : |‖distanceDifferenceLp μ p x y‖ - dist x y| ≤ δ) :
    |(bestApproximationCoordinatePair μ p v hv).pseudometric x y - dist x y| ≤ 2 * ε + δ := by
  have h := bestApproximation_pseudometric_error_le μ p v hv x y a b
  calc
    _ ≤ |(bestApproximationCoordinatePair μ p v hv).pseudometric x y - ‖distanceDifferenceLp μ p x y‖| +
        |‖distanceDifferenceLp μ p x y‖ - dist x y| := abs_sub_le _ _ _
    _ ≤ 2 * ε + δ := by linarith

theorem bestApproximation_pseudometric_error_of_uniform_competitors
    (v : ι → C(X, ℝ)) (hv : LinearIndependent ℝ v)
    (x y : X) (a b : EuclideanSpace ℝ ι) (ε δ : ℝ)
    (hx : ‖distanceProfile x - coordinateSynthesis v a‖ ≤ ε)
    (hy : ‖distanceProfile y - coordinateSynthesis v b‖ ≤ ε)
    (hd : |‖distanceDifferenceLp μ p x y‖ - dist x y| ≤ δ) :
    |(bestApproximationCoordinatePair μ p v hv).pseudometric x y - dist x y| ≤ 2 * ε + δ := by
  have hop : ‖(ContinuousMap.toLp p μ ℝ : C(X, ℝ) →L[ℝ] Lp ℝ p μ)‖ ≤ 1 := by
    simpa [measureUnivNNReal] using
      (ContinuousMap.toLp_norm_le (E := ℝ) (𝕜 := ℝ) (p := p) μ)
  have hcontract (f : C(X, ℝ)) : ‖ContinuousMap.toLp p μ ℝ f‖ ≤ ‖f‖ :=
    ((ContinuousMap.toLp p μ ℝ).le_opNorm f).trans
      (by nlinarith [norm_nonneg f])
  apply bestApproximation_pseudometric_dist_error_le μ p v hv x y a b ε δ
  · change ‖ContinuousMap.toLp p μ ℝ (distanceProfile x) -
      ContinuousMap.toLp p μ ℝ (coordinateSynthesis v a)‖ ≤ ε
    rw [← map_sub]
    exact (hcontract _).trans hx
  · change ‖ContinuousMap.toLp p μ ℝ (distanceProfile y) -
      ContinuousMap.toLp p μ ℝ (coordinateSynthesis v b)‖ ≤ ε
    rw [← map_sub]
    exact (hcontract _).trans hy
  · exact hd

end PaperN.PartII

namespace PaperN.PartII
open MeasureTheory Metric Set
variable {X ι : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X] [Fintype ι]
  (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
  (p : ENNReal) [Fact (1 ≤ p)] [StrictConvexSpace ℝ (Lp ℝ p μ)]

theorem bestApproximation_pseudometric_ball_mass_error
    (hp0 : p ≠ 0) (hp : p ≠ ⊤)
    (v : ι → C(X, ℝ)) (hv : LinearIndependent ℝ v)
    (r : ℝ) (hr : 0 < r) (ε : ℝ)
    (happrox : ∀ x : X, ∃ a : EuclideanSpace ℝ ι,
      ‖distanceProfile x - coordinateSynthesis v a‖ ≤ ε) (x y : X) :
    |(bestApproximationCoordinatePair μ p v hv).pseudometric x y - dist x y| ≤
      2 * ε + diam (univ : Set X) *
        (1 - (⨅ z : X, μ.real (ball z r)) ^ (1 / p.toReal)) + 2 * r := by
  obtain ⟨a, ha⟩ := happrox x
  obtain ⟨b, hb⟩ := happrox y
  have hd := distanceDifferenceLp_error μ p hp0 hp x y r hr
  have he : |‖distanceDifferenceLp μ p x y‖ - dist x y| ≤
      diam (univ : Set X) * (1 - (⨅ z : X, μ.real (ball z r)) ^ (1 / p.toReal)) + 2*r := by
    rw [abs_sub_comm, abs_of_nonneg hd.1]
    exact hd.2
  have h := bestApproximation_pseudometric_error_of_uniform_competitors μ p v hv x y a b ε _ ha hb he
  linarith

theorem bestApproximation_pseudometric_uniform_error
    (hp0 : p ≠ 0) (hp : p ≠ ⊤)
    (v : ι → C(X, ℝ)) (hv : LinearIndependent ℝ v)
    (r : ℝ) (hr : 0 < r) (ε : ℝ)
    (happrox : ∀ x : X, ∃ a : EuclideanSpace ℝ ι,
      ‖distanceProfile x - coordinateSynthesis v a‖ ≤ ε) :
    (⨆ z : X × X, |(bestApproximationCoordinatePair μ p v hv).pseudometric z.1 z.2 - dist z.1 z.2|) ≤
      2 * ε + diam (univ : Set X) *
        (1 - (⨅ z : X, μ.real (ball z r)) ^ (1 / p.toReal)) + 2 * r := by
  apply ciSup_le
  intro z
  exact bestApproximation_pseudometric_ball_mass_error μ p hp0 hp v hv r hr ε happrox z.1 z.2

end PaperN.PartII
