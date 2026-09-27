import PaperN.PartII.GramConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace PaperN.PartII
open MeasureTheory Filter Topology
variable {Z : Type*} [MetricSpace Z] [CompactSpace Z]

noncomputable def absPowerMap (q : ℝ) (hq : 0 ≤ q) : C(ℝ, ℝ) :=
  ⟨fun t ↦ |t| ^ q, continuous_abs.rpow_const (fun _ ↦ Or.inr hq)⟩

noncomputable def continuousAbsPower (q : ℝ) (hq : 0 ≤ q) (f : C(Z, ℝ)) : C(Z, ℝ) :=
  (absPowerMap q hq).comp f

omit [CompactSpace Z] in
theorem continuousAbsPower_tendsto (q : ℝ) (hq : 0 ≤ q)
    (fs : ℕ → C(Z, ℝ)) (f : C(Z, ℝ)) (hf : Tendsto fs atTop (𝓝 f)) :
    Tendsto (fun n ↦ continuousAbsPower q hq (fs n)) atTop (𝓝 (continuousAbsPower q hq f)) :=
  (absPowerMap q hq).continuous_postcomp.continuousAt.tendsto.comp hf

variable [MeasurableSpace Z] [BorelSpace Z]

theorem varying_absPower_integral_tendsto
    (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z)
    (hμ : Tendsto μs atTop (𝓝 μ)) (q : ℝ) (hq : 0 ≤ q)
    (fs : ℕ → C(Z, ℝ)) (f : C(Z, ℝ)) (hf : Tendsto fs atTop (𝓝 f)) :
    Tendsto (fun n ↦ ∫ z, |fs n z| ^ q ∂(μs n : Measure Z)) atTop
      (𝓝 (∫ z, |f z| ^ q ∂(μ : Measure Z))) :=
  varying_integral_tendsto μs μ hμ _ _ (continuousAbsPower_tendsto q hq fs f hf)

end PaperN.PartII

namespace PaperN.PartII
open MeasureTheory Filter Topology
variable {Z P : Type*} [MetricSpace Z] [CompactSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [MetricSpace P] [CompactSpace P]

theorem varying_absPower_integral_uniform
    (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z)
    (hμ : Tendsto μs atTop (𝓝 μ)) (q : ℝ) (hq : 0 ≤ q)
    (Fs : ℕ → C(P × Z, ℝ)) (F : C(P × Z, ℝ)) (hF : Tendsto Fs atTop (𝓝 F)) :
    TendstoUniformly (fun n a ↦ ∫ z, |Fs n (a, z)| ^ q ∂(μs n : Measure Z))
      (fun a ↦ ∫ z, |F (a, z)| ^ q ∂(μ : Measure Z)) atTop := by
  have hp := continuousAbsPower_tendsto q hq Fs F hF
  apply PartI.parameterIntegrals_uniform μs μ hμ
    (fun n ↦ continuousAbsPower q hq (Fs n)) (continuousAbsPower q hq F)
  simpa using (hp.sub (tendsto_const_nhds (x := continuousAbsPower q hq F))).norm

end PaperN.PartII
