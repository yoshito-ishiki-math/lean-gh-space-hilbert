import PaperN.PartII.ObjectiveLpNorm

namespace PaperN.PartII
open MeasureTheory Filter Topology
variable {Z : Type*} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]

theorem varying_continuous_Lp_norm_tendsto
    (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z)
    (hμ : Tendsto μs atTop (𝓝 μ)) (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (fs : ℕ → C(Z, ℝ)) (f : C(Z, ℝ)) (hf : Tendsto fs atTop (𝓝 f)) :
    Tendsto (fun n ↦ ‖ContinuousMap.toLp p (μs n : Measure Z) ℝ (fs n)‖) atTop
      (𝓝 ‖ContinuousMap.toLp p (μ : Measure Z) ℝ f‖) := by
  have hp0 : p.toReal ≠ 0 :=
    (ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp).ne'
  have hi := varying_absPower_integral_tendsto μs μ hμ p.toReal ENNReal.toReal_nonneg fs f hf
  have hc : Continuous (fun t : ℝ ↦ t ^ p.toReal⁻¹) :=
    continuous_id.rpow_const (fun _ ↦ Or.inr (inv_nonneg.mpr ENNReal.toReal_nonneg))
  have ht := hc.continuousAt.tendsto.comp hi
  simp only [Function.comp_def, ← continuous_toLp_norm_rpow _ p hp,
    Real.rpow_rpow_inv (norm_nonneg _) hp0] at ht
  exact ht

theorem coordinateLpNorm_tendsto {ι : Type*} [Fintype ι]
    (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z)
    (hμ : Tendsto μs atTop (𝓝 μ)) (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (vs : ℕ → ι → C(Z, ℝ)) (v : ι → C(Z, ℝ))
    (hv : ∀ i, Tendsto (fun n ↦ vs n i) atTop (𝓝 (v i)))
    (as : ℕ → EuclideanSpace ℝ ι) (a : EuclideanSpace ℝ ι)
    (ha : Tendsto as atTop (𝓝 a)) :
    Tendsto (fun n ↦ coordinateLpNorm (μs n : Measure Z) p (vs n) (as n)) atTop
      (𝓝 (coordinateLpNorm (μ : Measure Z) p v a)) := by
  apply varying_continuous_Lp_norm_tendsto μs μ hμ p hp
  change Tendsto (fun n ↦ ∑ i, as n i • vs n i) atTop (𝓝 (∑ i, a i • v i))
  apply tendsto_finsetSum
  intro i _
  exact (((PiLp.continuous_apply 2 (fun _ : ι ↦ ℝ) i).tendsto a).comp ha).smul (hv i)

end PaperN.PartII
