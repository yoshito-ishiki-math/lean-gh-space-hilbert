import PaperN.PartII.LpNormConvergence

namespace PaperN.PartII
open MeasureTheory Filter Topology
variable {Z ι : Type*} [MetricSpace Z] [CompactSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [Fintype ι]

theorem coordinateLpNorm_uniform_on_compact
    (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z)
    (hμ : Tendsto μs atTop (𝓝 μ)) (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (vs : ℕ → ι → C(Z, ℝ)) (v : ι → C(Z, ℝ))
    (hv : ∀ i, Tendsto (fun n ↦ vs n i) atTop (𝓝 (v i)))
    (K : Set (EuclideanSpace ℝ ι)) (hK : IsCompact K) :
    TendstoUniformly (fun n (a : K) ↦ coordinateLpNorm (μs n : Measure Z) p (vs n) a)
      (fun a : K ↦ coordinateLpNorm (μ : Measure Z) p v a) atTop := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let A : C(K, EuclideanSpace ℝ ι) := ⟨Subtype.val, continuous_subtype_val⟩
  let N (ν : ProbabilityMeasure Z) (w : ι → C(Z, ℝ)) : C(K, ℝ) :=
    ⟨fun a ↦ coordinateLpNorm (ν : Measure Z) p w a,
      (seminorm_continuous_finiteDimensional _).comp continuous_subtype_val⟩
  let Q (ν : ProbabilityMeasure Z) (w : ι → C(Z, ℝ)) : C(K, ℝ) :=
    ⟨fun a ↦ (N ν w a) ^ p.toReal,
      (N ν w).continuous.rpow_const (fun _ ↦ Or.inr ENNReal.toReal_nonneg)⟩
  have hq : Tendsto (fun n ↦ Q (μs n) (vs n)) atTop (𝓝 (Q μ v)) := by
    apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
    have h := synthesis_power_integrals_uniform A μs μ hμ p.toReal
      ENNReal.toReal_nonneg vs v hv
    have heq (ν : ProbabilityMeasure Z) (w : ι → C(Z, ℝ)) (a : K) :
        Q ν w a = ∫ z, |∑ i, A a i * w i z| ^ p.toReal ∂(ν : Measure Z) := by
      change ‖ContinuousMap.toLp p (ν : Measure Z) ℝ (coordinateSynthesis w a)‖ ^ p.toReal = _
      rw [continuous_toLp_norm_rpow _ p hp]
      simp [coordinateSynthesis, A, Fintype.linearCombination_apply]
    change TendstoUniformly (fun n a ↦ Q (μs n) (vs n) a) (fun a ↦ Q μ v a) atTop
    simpa only [heq] using h
  let R : C(ℝ, ℝ) := ⟨fun t ↦ t ^ p.toReal⁻¹,
    continuous_id.rpow_const (fun _ ↦ Or.inr (inv_nonneg.mpr ENNReal.toReal_nonneg))⟩
  have hr := R.continuous_postcomp.continuousAt.tendsto.comp hq
  have hp0 : p.toReal ≠ 0 :=
    (ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp).ne'
  have heq (ν : ProbabilityMeasure Z) (w : ι → C(Z, ℝ)) : R.comp (Q ν w) = N ν w := by
    ext a
    exact Real.rpow_rpow_inv (norm_nonneg (coordinateLpMap (ν : Measure Z) p w a)) hp0
  have hn : Tendsto (fun n ↦ N (μs n) (vs n)) atTop (𝓝 (N μ v)) := by
    simpa only [Function.comp_def, heq] using hr
  exact ContinuousMap.tendsto_iff_tendstoUniformly.mp hn

theorem coordinateLpNorm_uniform_on_ball
    (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z)
    (hμ : Tendsto μs atTop (𝓝 μ)) (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (vs : ℕ → ι → C(Z, ℝ)) (v : ι → C(Z, ℝ))
    (hv : ∀ i, Tendsto (fun n ↦ vs n i) atTop (𝓝 (v i))) (R : ℝ) :
    TendstoUniformlyOn (fun n a ↦ coordinateLpNorm (μs n : Measure Z) p (vs n) a)
      (fun a ↦ coordinateLpNorm (μ : Measure Z) p v a) atTop
      (Metric.closedBall (0 : EuclideanSpace ℝ ι) R) :=
  tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    (coordinateLpNorm_uniform_on_compact μs μ hμ p hp vs v hv _ (isCompact_closedBall _ _))

end PaperN.PartII
