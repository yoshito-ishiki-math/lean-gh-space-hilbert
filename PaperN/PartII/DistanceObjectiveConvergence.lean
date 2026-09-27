import PaperN.PartII.ParameterizedSynthesis

namespace PaperN.PartII
open MeasureTheory Filter Topology
variable {Z ι : Type*} [MetricSpace Z] [CompactSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [Fintype ι]

noncomputable def distanceObjective (μ : ProbabilityMeasure Z) (q : ℝ)
    (v : ι → C(Z, ℝ)) (x : Z) (a : EuclideanSpace ℝ ι) : ℝ :=
  ∫ z, |dist x z - ∑ i, a i * v i z| ^ q ∂(μ : Measure Z)

theorem distanceObjective_uniform_on_compact
    (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z)
    (hμ : Tendsto μs atTop (𝓝 μ)) (q : ℝ) (hq : 0 ≤ q)
    (vs : ℕ → ι → C(Z, ℝ)) (v : ι → C(Z, ℝ))
    (hv : ∀ i, Tendsto (fun n ↦ vs n i) atTop (𝓝 (v i)))
    (K : Set (EuclideanSpace ℝ ι)) (hK : IsCompact K) :
    TendstoUniformly (fun n (p : Z × K) ↦ distanceObjective (μs n) q (vs n) p.1 p.2)
      (fun p : Z × K ↦ distanceObjective μ q v p.1 p.2) atTop := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let A : C(Z × K, EuclideanSpace ℝ ι) :=
    ⟨fun p ↦ p.2.val, continuous_subtype_val.comp continuous_snd⟩
  let D : C((Z × K) × Z, ℝ) :=
    ⟨fun p ↦ dist p.1.1 p.2, (continuous_fst.comp continuous_fst).dist continuous_snd⟩
  exact residual_power_integrals_uniform A μs μ hμ q hq vs v hv
    (fun _ ↦ D) D tendsto_const_nhds

theorem distanceObjective_uniform_on_ball
    (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z)
    (hμ : Tendsto μs atTop (𝓝 μ)) (q : ℝ) (hq : 0 ≤ q)
    (vs : ℕ → ι → C(Z, ℝ)) (v : ι → C(Z, ℝ))
    (hv : ∀ i, Tendsto (fun n ↦ vs n i) atTop (𝓝 (v i))) (R : ℝ) :
    TendstoUniformly
      (fun n (p : Z × Metric.closedBall (0 : EuclideanSpace ℝ ι) R) ↦
        distanceObjective (μs n) q (vs n) p.1 p.2)
      (fun p : Z × Metric.closedBall (0 : EuclideanSpace ℝ ι) R ↦
        distanceObjective μ q v p.1 p.2) atTop :=
  distanceObjective_uniform_on_compact μs μ hμ q hq vs v hv _ (isCompact_closedBall _ _)

theorem distanceObjective_sup_error_tendsto [Nonempty Z]
    (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z)
    (hμ : Tendsto μs atTop (𝓝 μ)) (q : ℝ) (hq : 0 ≤ q)
    (vs : ℕ → ι → C(Z, ℝ)) (v : ι → C(Z, ℝ))
    (hv : ∀ i, Tendsto (fun n ↦ vs n i) atTop (𝓝 (v i)))
    (K : Set (EuclideanSpace ℝ ι)) (hK : IsCompact K) (hne : K.Nonempty) :
    Tendsto (fun n ↦ ⨆ p : Z × K,
      |distanceObjective (μs n) q (vs n) p.1 p.2 - distanceObjective μ q v p.1 p.2|)
      atTop (𝓝 0) := by
  letI : Nonempty K := hne.to_subtype
  simpa only [Real.dist_eq] using PartI.tendsto_sup_dist_of_uniform
    (distanceObjective_uniform_on_compact μs μ hμ q hq vs v hv K hK)

end PaperN.PartII
