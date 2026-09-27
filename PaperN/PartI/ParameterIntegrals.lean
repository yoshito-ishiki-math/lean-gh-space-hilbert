import PaperN.PartI.MetricBump
import PaperN.PartI.ParameterIntegralStatements
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.ContinuousMap.Compact

set_option backward.isDefEq.respectTransparency false

namespace PaperN.PartI
open MeasureTheory Filter TopologicalSpace
open scoped Topology BoundedContinuousFunction
variable {Z P 𝕜 : Type*} [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [RCLike 𝕜]

/-- Probability integration is a contraction in the uniform norm. -/
theorem dist_integral_le_uniform (μ : ProbabilityMeasure Z) (f g : Z →ᵇ 𝕜) :
    dist (∫ z, f z ∂(μ : Measure Z)) (∫ z, g z ∂(μ : Measure Z)) ≤ dist f g := by
  rw [dist_eq_norm, ← integral_sub (f.integrable _) (g.integrable _), dist_eq_norm]
  exact (f - g).norm_integral_le_norm (μ : Measure Z)

/-- Weak convergence is uniform for a continuously parametrized compact family of tests. -/
theorem uniform_integrals_of_compact_parameters [TopologicalSpace P] [CompactSpace P]
    (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z)
    (hμ : Tendsto μs atTop (𝓝 μ)) (F : C(P, Z →ᵇ 𝕜)) :
    TendstoUniformly (fun n p ↦ ∫ z, F p z ∂(μs n : Measure Z))
      (fun p ↦ ∫ z, F p z ∂(μ : Measure Z)) atTop := by
  have he : Equicontinuous (fun n p ↦ ∫ z, F p z ∂(μs n : Measure Z)) := by
    intro p
    apply Metric.equicontinuousAt_of_continuity_modulus (fun q ↦ dist (F p) (F q))
      (by simpa using ((continuous_const : Continuous (fun _ : P ↦ F p)).dist F.continuous).tendsto p)
    exact Filter.Eventually.of_forall fun q n ↦ dist_integral_le_uniform (μs n) (F p) (F q)
  apply UniformFun.tendsto_iff_tendstoUniformly.mp
  apply (he.tendsto_uniformFun_iff_pi atTop _).mpr
  exact tendsto_pi_nhds.mpr fun p ↦
    (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto 𝕜).mp hμ (F p)

/-- `lem:uniform-weak-integrals`, in uniform-convergence form, for real or complex tests. -/
theorem uniformWeakIntegrals_uniform
    (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z)
    (hμ : Tendsto μs atTop (𝓝 μ)) (K : Set (Z →ᵇ 𝕜)) (hK : IsCompact K) :
    TendstoUniformly (fun n (f : K) ↦ ∫ z, f.val z ∂(μs n : Measure Z))
      (fun (f : K) ↦ ∫ z, f.val z ∂(μ : Measure Z)) atTop := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact uniform_integrals_of_compact_parameters μs μ hμ ⟨Subtype.val, continuous_subtype_val⟩

/-- Uniform convergence gives the exact supremum-of-errors formulation used in the paper. -/
theorem tendsto_sup_dist_of_uniform {A E : Type*} [Nonempty A] [MetricSpace E]
    {fs : ℕ → A → E} {f : A → E} (h : TendstoUniformly fs f atTop) :
    Tendsto (fun n ↦ ⨆ a, dist (fs n a) (f a)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp h (ε / 2) (half_pos hε)] with n hn
  have hb : BddAbove (Set.range (fun a ↦ dist (fs n a) (f a))) := by
    refine ⟨ε / 2, ?_⟩
    rintro _ ⟨a, rfl⟩
    simpa only [dist_comm] using (hn a).le
  have hlo : 0 ≤ ⨆ a, dist (fs n a) (f a) :=
    dist_nonneg.trans (le_ciSup hb (Classical.choice inferInstance))
  have hhi : (⨆ a, dist (fs n a) (f a)) ≤ ε / 2 :=
    ciSup_le fun a ↦ by simpa only [dist_comm] using (hn a).le
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hlo] using
    hhi.trans_lt (half_lt_self hε)

/-- `lem:parameter-integrals`, including uniformly varying real or complex integrands. -/
theorem parameterIntegrals_uniform [MetricSpace P] [CompactSpace P] [CompactSpace Z]
    (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z)
    (hμ : Tendsto μs atTop (𝓝 μ))
    (Fs : ℕ → C(P × Z, 𝕜)) (F : C(P × Z, 𝕜))
    (hF : Tendsto (fun n ↦ ‖Fs n - F‖) atTop (𝓝 0)) :
    TendstoUniformly (fun n p ↦ ∫ z, Fs n (p, z) ∂(μs n : Measure Z))
      (fun p ↦ ∫ z, F (p, z) ∂(μ : Measure Z)) atTop := by
  let G : C(P, Z →ᵇ 𝕜) :=
    ⟨fun p ↦ BoundedContinuousFunction.mkOfCompact (F.curry p),
      (ContinuousMap.isometryEquivBoundedOfCompact Z 𝕜).continuous.comp F.curry.continuous⟩
  have hG := uniform_integrals_of_compact_parameters μs μ hμ G
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have h1 := hF.eventually (gt_mem_nhds (half_pos hε))
  have h2 := Metric.tendstoUniformly_iff.mp hG (ε / 2) (half_pos hε)
  filter_upwards [h1, h2] with n hn hnp
  intro p
  have hi : dist (∫ z, F (p, z) ∂(μs n : Measure Z))
      (∫ z, Fs n (p, z) ∂(μs n : Measure Z)) ≤ ‖Fs n - F‖ := by
    have hs : Integrable (fun z ↦ Fs n (p, z)) (μs n : Measure Z) :=
      (BoundedContinuousFunction.mkOfCompact ((Fs n).curry p)).integrable _
    have hf : Integrable (fun z ↦ F (p, z)) (μs n : Measure Z) :=
      (BoundedContinuousFunction.mkOfCompact (F.curry p)).integrable _
    rw [dist_comm, dist_eq_norm, ← integral_sub hs hf]
    have hb : ∀ᵐ z ∂(μs n : Measure Z), ‖Fs n (p, z) - F (p, z)‖ ≤ ‖Fs n - F‖ :=
      ae_of_all _ fun z ↦ (Fs n - F).norm_coe_le_norm (p, z)
    simpa using norm_integral_le_of_norm_le_const hb
  have ht := dist_triangle (∫ z, F (p, z) ∂(μ : Measure Z))
    (∫ z, F (p, z) ∂(μs n : Measure Z)) (∫ z, Fs n (p, z) ∂(μs n : Measure Z))
  have hp := hnp p
  change dist (∫ z, F (p, z) ∂(μ : Measure Z))
    (∫ z, F (p, z) ∂(μs n : Measure Z)) < ε / 2 at hp
  linarith

/-- The ambient ball-mass functions in `lem:full-support-gdelta` converge uniformly. -/
theorem ballMass_tendstoUniformly [CompactSpace Z]
    (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z)
    (hμ : Tendsto μs atTop (𝓝 μ)) (r : ℝ) :
    TendstoUniformly (fun n x ↦ ∫ z, metricBump x r z ∂(μs n : Measure Z))
      (fun x ↦ ∫ z, metricBump x r z ∂(μ : Measure Z)) atTop := by
  let F : C(Z × Z, ℝ) := ⟨fun p ↦ metricBump p.1 r p.2, by unfold metricBump; fun_prop⟩
  exact parameterIntegrals_uniform μs μ hμ (fun _ ↦ F) F (by simp)

/-- The supremum formulation of the entire compact-test-family lemma. -/
theorem uniformWeakIntegrals_spec [CompactSpace Z] : UniformWeakIntegralsStatement Z 𝕜 := by
  intro μs μ hμ K hK hKne
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : Nonempty K := hKne.to_subtype
  let F : C(K, Z →ᵇ 𝕜) := ⟨fun f ↦ BoundedContinuousFunction.mkOfCompact f.val,
    (ContinuousMap.isometryEquivBoundedOfCompact Z 𝕜).continuous.comp continuous_subtype_val⟩
  simpa [dist_eq_norm, F] using tendsto_sup_dist_of_uniform
    (uniform_integrals_of_compact_parameters μs μ hμ F)

/-- The supremum formulation of the entire parameter-integral lemma. -/
theorem parameterIntegrals_spec [MetricSpace P] [CompactSpace P] [Nonempty P]
    [CompactSpace Z] : ParameterIntegralsStatement Z P 𝕜 := by
  intro μs μ hμ Fs F hF
  simpa only [dist_eq_norm] using tendsto_sup_dist_of_uniform
    (parameterIntegrals_uniform μs μ hμ Fs F hF)

end PaperN.PartI
