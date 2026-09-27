import PaperN.PartII.PowerIntegralConvergence
import PaperN.PartII.CoordinateLpNorm

namespace PaperN.PartII
open Filter Topology MeasureTheory
variable {P Z ι : Type*} [MetricSpace P] [CompactSpace P]
  [MetricSpace Z] [CompactSpace Z] [Fintype ι]

noncomputable def coefficientOnProduct (A : C(P, EuclideanSpace ℝ ι)) (i : ι) : C(P × Z, ℝ) :=
  ⟨fun z ↦ A z.1 i, (PiLp.continuous_apply 2 (fun _ : ι ↦ ℝ) i).comp (A.continuous.comp continuous_fst)⟩

noncomputable def parameterizedSynthesis (A : C(P, EuclideanSpace ℝ ι))
    (v : ι → C(Z, ℝ)) : C(P × Z, ℝ) :=
  ∑ i, coefficientOnProduct A i * (v i).comp ⟨Prod.snd, continuous_snd⟩

theorem parameterizedSynthesis_tendsto (A : C(P, EuclideanSpace ℝ ι))
    (vs : ℕ → ι → C(Z, ℝ)) (v : ι → C(Z, ℝ))
    (hv : ∀ i, Tendsto (fun n ↦ vs n i) atTop (𝓝 (v i))) :
    Tendsto (fun n ↦ parameterizedSynthesis A (vs n)) atTop (𝓝 (parameterizedSynthesis A v)) := by
  apply tendsto_finsetSum
  intro i _
  exact tendsto_const_nhds.mul
    ((ContinuousMap.continuous_precomp (⟨Prod.snd, continuous_snd⟩ : C(P × Z, Z))).continuousAt.tendsto.comp (hv i))

variable [MeasurableSpace Z] [BorelSpace Z]

theorem synthesis_power_integrals_uniform (A : C(P, EuclideanSpace ℝ ι))
    (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z)
    (hμ : Tendsto μs atTop (𝓝 μ)) (q : ℝ) (hq : 0 ≤ q)
    (vs : ℕ → ι → C(Z, ℝ)) (v : ι → C(Z, ℝ))
    (hv : ∀ i, Tendsto (fun n ↦ vs n i) atTop (𝓝 (v i))) :
    TendstoUniformly (fun n a ↦ ∫ z, |∑ i, A a i * vs n i z| ^ q ∂(μs n : Measure Z))
      (fun a ↦ ∫ z, |∑ i, A a i * v i z| ^ q ∂(μ : Measure Z)) atTop := by
  have h := varying_absPower_integral_uniform μs μ hμ q hq
    (fun n ↦ parameterizedSynthesis A (vs n)) (parameterizedSynthesis A v)
    (parameterizedSynthesis_tendsto A vs v hv)
  simpa [parameterizedSynthesis, coefficientOnProduct] using h

theorem residual_power_integrals_uniform (A : C(P, EuclideanSpace ℝ ι))
    (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z)
    (hμ : Tendsto μs atTop (𝓝 μ)) (q : ℝ) (hq : 0 ≤ q)
    (vs : ℕ → ι → C(Z, ℝ)) (v : ι → C(Z, ℝ))
    (hv : ∀ i, Tendsto (fun n ↦ vs n i) atTop (𝓝 (v i)))
    (Ds : ℕ → C(P × Z, ℝ)) (D : C(P × Z, ℝ)) (hD : Tendsto Ds atTop (𝓝 D)) :
    TendstoUniformly
      (fun n a ↦ ∫ z, |Ds n (a,z) - ∑ i, A a i * vs n i z| ^ q ∂(μs n : Measure Z))
      (fun a ↦ ∫ z, |D (a,z) - ∑ i, A a i * v i z| ^ q ∂(μ : Measure Z)) atTop := by
  have h := varying_absPower_integral_uniform μs μ hμ q hq
    (fun n ↦ Ds n - parameterizedSynthesis A (vs n)) (D - parameterizedSynthesis A v)
    (hD.sub (parameterizedSynthesis_tendsto A vs v hv))
  simpa [parameterizedSynthesis, coefficientOnProduct] using h

end PaperN.PartII
