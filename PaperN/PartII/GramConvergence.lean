import PaperN.PartI.ParameterIntegrals
import Mathlib.Topology.Instances.Matrix

namespace PaperN.PartII
open MeasureTheory Filter
open scoped Topology
variable {Z : Type*} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]

theorem varying_integral_tendsto
    (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z)
    (hμ : Tendsto μs atTop (𝓝 μ)) (fs : ℕ → C(Z, ℝ)) (f : C(Z, ℝ))
    (hf : Tendsto fs atTop (𝓝 f)) :
    Tendsto (fun n ↦ ∫ z, fs n z ∂(μs n : Measure Z)) atTop
      (𝓝 (∫ z, f z ∂(μ : Measure Z))) := by
  have hfixed := (ProbabilityMeasure.continuous_integral_continuousMap f).tendsto μ |>.comp hμ
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp hf (ε / 2) (half_pos hε),
    Metric.tendsto_nhds.mp hfixed (ε / 2) (half_pos hε)] with n hn hm
  have hb : dist (∫ z, fs n z ∂(μs n : Measure Z))
      (∫ z, f z ∂(μs n : Measure Z)) ≤ dist (fs n) f := by
    have h := PartI.dist_integral_le_uniform (μs n)
      (BoundedContinuousFunction.mkOfCompact (fs n)) (BoundedContinuousFunction.mkOfCompact f)
    simpa using h
  exact (dist_triangle _ _ _).trans_lt (add_lt_add (hb.trans_lt hn) hm) |>.trans_eq (by ring)

noncomputable def continuousGram {ι : Type*} (μ : ProbabilityMeasure Z)
    (v : ι → C(Z, ℝ)) : Matrix ι ι ℝ :=
  fun i j ↦ ∫ z, v i z * v j z ∂(μ : Measure Z)

theorem continuousGram_tendsto {ι : Type*}
    (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z)
    (hμ : Tendsto μs atTop (𝓝 μ)) (vs : ℕ → ι → C(Z, ℝ)) (v : ι → C(Z, ℝ))
    (hv : ∀ i, Tendsto (fun n ↦ vs n i) atTop (𝓝 (v i))) :
    Tendsto (fun n ↦ continuousGram (μs n) (vs n)) atTop (𝓝 (continuousGram μ v)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact varying_integral_tendsto μs μ hμ (fun n ↦ vs n i * vs n j) (v i * v j)
    ((hv i).mul (hv j))

theorem continuousGram_eventually_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z)
    (hμ : Tendsto μs atTop (𝓝 μ)) (vs : ℕ → ι → C(Z, ℝ)) (v : ι → C(Z, ℝ))
    (hv : ∀ i, Tendsto (fun n ↦ vs n i) atTop (𝓝 (v i)))
    (horth : continuousGram μ v = 1) :
    ∀ᶠ n in atTop, IsUnit (continuousGram (μs n) (vs n)) := by
  have hg := continuousGram_tendsto μs μ hμ vs v hv
  rw [horth] at hg
  have hd := (continuous_id.matrix_det.tendsto (1 : Matrix ι ι ℝ)).comp hg
  simp only [id_eq, Matrix.det_one] at hd
  have hn : ∀ᶠ n in atTop, (continuousGram (μs n) (vs n)).det ≠ 0 :=
    hd.eventually (by
      exact eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0))
  filter_upwards [hn] with n hn
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hn)

end PaperN.PartII
