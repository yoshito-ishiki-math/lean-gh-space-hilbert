import PaperN.PartII.DistanceObjectiveConvergence
import PaperN.PartII.MinimizerContinuity

namespace PaperN.PartII
open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction
variable {Z ι : Type*} [MetricSpace Z] [CompactSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [Fintype ι]

/-- The objective is jointly continuous in the ambient point and all coefficients. -/
theorem continuous_distanceObjective (μ : ProbabilityMeasure Z) (q : ℝ) (hq : 0 ≤ q)
    (v : ι → C(Z, ℝ)) :
    Continuous (fun p : Z × EuclideanSpace ℝ ι ↦ distanceObjective μ q v p.1 p.2) := by
  let F : C((Z × EuclideanSpace ℝ ι) × Z, ℝ) :=
    ⟨fun p ↦ |dist p.1.1 p.2 - ∑ i, p.1.2 i * v i p.2| ^ q, by
      apply Continuous.rpow_const _ (fun _ ↦ Or.inr hq)
      apply Continuous.abs
      apply Continuous.sub ((continuous_fst.comp continuous_fst).dist continuous_snd)
      exact continuous_finsetSum _ fun i _ ↦
        ((PiLp.continuous_apply 2 (fun _ : ι ↦ ℝ) i).comp
          (continuous_snd.comp continuous_fst)).mul ((v i).continuous.comp continuous_snd)⟩
  have hi : LipschitzWith 1 (fun f : Z →ᵇ ℝ ↦ ∫ z, f z ∂(μ : Measure Z)) := by
    apply LipschitzWith.of_dist_le_mul
    intro f g
    simpa using PartI.dist_integral_le_uniform μ f g
  exact hi.continuous.comp
    ((ContinuousMap.isometryEquivBoundedOfCompact Z ℝ).continuous.comp F.curry.continuous)

/-- Uniform objective convergence on compact coefficient sets also allows moving basepoints. -/
theorem distanceObjective_moving_uniform_on_compact
    (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z)
    (hμ : Tendsto μs atTop (𝓝 μ)) (q : ℝ) (hq : 0 ≤ q)
    (vs : ℕ → ι → C(Z, ℝ)) (v : ι → C(Z, ℝ))
    (hv : ∀ i, Tendsto (fun n ↦ vs n i) atTop (𝓝 (v i)))
    (xs : ℕ → Z) (x : Z) (hx : Tendsto xs atTop (𝓝 x))
    (K : Set (EuclideanSpace ℝ ι)) (hK : IsCompact K) :
    TendstoUniformly (fun n (a : K) ↦ distanceObjective (μs n) q (vs n) (xs n) a)
      (fun a : K ↦ distanceObjective μ q v x a) atTop := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let A : C(K, EuclideanSpace ℝ ι) := ⟨Subtype.val, continuous_subtype_val⟩
  let D : Z → C(K × Z, ℝ) := fun y ↦
    ⟨fun p ↦ dist y p.2, continuous_const.dist continuous_snd⟩
  have hD : Tendsto (fun n ↦ D (xs n)) atTop (𝓝 (D x)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun n ↦ norm_nonneg _) _
      (by simpa using hx.dist (tendsto_const_nhds (x := x)))
    intro n
    apply (ContinuousMap.norm_le _ dist_nonneg).mpr
    intro p
    exact abs_dist_sub_le (xs n) x p.2
  exact residual_power_integrals_uniform A μs μ hμ q hq vs v hv
    (fun n ↦ D (xs n)) (D x) hD

/-- Application to actual objective minimizers; boundedness and uniqueness remain explicit. -/
theorem distanceObjective_minimizers_tendsto
    (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z)
    (hμ : Tendsto μs atTop (𝓝 μ)) (q : ℝ) (hq : 0 ≤ q)
    (vs : ℕ → ι → C(Z, ℝ)) (v : ι → C(Z, ℝ))
    (hv : ∀ i, Tendsto (fun n ↦ vs n i) atTop (𝓝 (v i)))
    (xs : ℕ → Z) (x : Z) (hx : Tendsto xs atTop (𝓝 x))
    (u : ℕ → EuclideanSpace ℝ ι) (a : EuclideanSpace ℝ ι)
    (hb : Bornology.IsBounded (Set.range u))
    (hm : ∀ n b, distanceObjective (μs n) q (vs n) (xs n) (u n) ≤
      distanceObjective (μs n) q (vs n) (xs n) b)
    (hunique : ∀ b, (∀ c, distanceObjective μ q v x b ≤ distanceObjective μ q v x c) →
      b = a) : Tendsto u atTop (𝓝 a) := by
  apply minimizer_tendsto _ _ u a
    ((continuous_distanceObjective μ q hq v).comp (continuous_const.prodMk continuous_id))
    _ hb hm hunique
  intro K hK
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    (distanceObjective_moving_uniform_on_compact μs μ hμ q hq vs v hv xs x hx K hK)

end PaperN.PartII
