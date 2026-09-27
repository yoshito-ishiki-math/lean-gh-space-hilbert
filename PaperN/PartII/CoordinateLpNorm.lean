import PaperN.PartII.NormedCoordinateClass
import PaperN.PartII.DistanceKernel

namespace PaperN.PartII
open MeasureTheory
variable {X ι : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Fintype ι]

/-- Synthesis of a continuous function from Euclidean coefficients. -/
noncomputable def coordinateSynthesis (v : ι → C(X, ℝ)) :
    EuclideanSpace ℝ ι →ₗ[ℝ] C(X, ℝ) :=
  (Fintype.linearCombination ℝ v).comp (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toLinearMap

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem coordinateSynthesis_injective (v : ι → C(X, ℝ)) (hv : LinearIndependent ℝ v) :
    Function.Injective (coordinateSynthesis v) :=
  (linearIndependent_iff_injective_fintypeLinearCombination.mp hv).comp
    (WithLp.linearEquiv 2 ℝ (ι → ℝ)).injective

variable (μ : Measure X) [IsFiniteMeasure μ] (p : ENNReal) [Fact (1 ≤ p)]

noncomputable def coordinateLpMap (v : ι → C(X, ℝ)) :
    EuclideanSpace ℝ ι →ₗ[ℝ] Lp ℝ p μ :=
  (ContinuousMap.toLp p μ ℝ).toLinearMap.comp (coordinateSynthesis v)

noncomputable def coordinateLpNorm (v : ι → C(X, ℝ)) : Seminorm ℝ (EuclideanSpace ℝ ι) :=
  (normSeminorm ℝ (Lp ℝ p μ)).comp (coordinateLpMap μ p v)

theorem coordinateLpNorm_apply (v : ι → C(X, ℝ)) (a : EuclideanSpace ℝ ι) :
    coordinateLpNorm μ p v a = ‖ContinuousMap.toLp p μ ℝ (coordinateSynthesis v a)‖ := rfl

theorem coordinateLpNorm_definite [μ.IsOpenPosMeasure]
    (v : ι → C(X, ℝ)) (hv : LinearIndependent ℝ v)
    (a : EuclideanSpace ℝ ι) (ha : coordinateLpNorm μ p v a = 0) : a = 0 := by
  have h : coordinateLpMap μ p v a = 0 := norm_eq_zero.mp ha
  have hi : Function.Injective (coordinateLpMap μ p v) :=
    (ContinuousMap.toLp_injective μ).comp (coordinateSynthesis_injective v hv)
  exact hi (h.trans (map_zero _).symm)

/-- A continuous coefficient selection yields a genuine normed coordinate pair. -/
noncomputable def coordinateLpPair [μ.IsOpenPosMeasure]
    (v : ι → C(X, ℝ)) (hv : LinearIndependent ℝ v)
    (f : C(X, EuclideanSpace ℝ ι)) : NormedCoordinatePair X (EuclideanSpace ℝ ι) where
  coordinates := f
  norm := coordinateLpNorm μ p v
  definite := coordinateLpNorm_definite μ p v hv

end PaperN.PartII

namespace PaperN.PartII
open MeasureTheory Metric Set
variable {X ι : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Fintype ι]
  (μ : Measure X) [IsProbabilityMeasure μ] (p : ENNReal) [Fact (1 ≤ p)]

/-- Minimality against the zero competitor gives the local-model norm bound. -/
theorem coordinateLpNorm_le_two_diam (v : ι → C(X, ℝ))
    (x : X) (a : EuclideanSpace ℝ ι)
    (hmin : ‖ContinuousMap.toLp p μ ℝ (distanceProfile x) - coordinateLpMap μ p v a‖ ≤
      ‖ContinuousMap.toLp p μ ℝ (distanceProfile x)‖) :
    coordinateLpNorm μ p v a ≤ 2 * diam (univ : Set X) := by
  let d := ContinuousMap.toLp p μ ℝ (distanceProfile x)
  let b := coordinateLpMap μ p v a
  have hop : ‖(ContinuousMap.toLp p μ ℝ : C(X, ℝ) →L[ℝ] Lp ℝ p μ)‖ ≤ 1 := by
    simpa [measureUnivNNReal] using
      (ContinuousMap.toLp_norm_le (E := ℝ) (𝕜 := ℝ) (p := p) μ)
  have hd : ‖d‖ ≤ diam (univ : Set X) := by
    have h := (ContinuousMap.toLp p μ ℝ).le_opNorm (distanceProfile x)
    have ht : ‖d‖ ≤ ‖distanceProfile x‖ :=
      h.trans (by nlinarith [norm_nonneg (distanceProfile x)])
    exact ht.trans (distanceProfile_norm_le x)
  have hb : ‖b‖ ≤ ‖d‖ + ‖d - b‖ := by
    calc
      ‖b‖ = ‖d - (d - b)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖d‖ + ‖d - b‖ := norm_sub_le _ _
  change ‖b‖ ≤ _
  change ‖d - b‖ ≤ ‖d‖ at hmin
  linarith

end PaperN.PartII
