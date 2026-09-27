import PaperN.PartII.AmbientCompact
import PaperN.PartI.ParameterIntegrals

namespace PaperN.PartII.AmbientKernel
open MeasureTheory Metric Set Filter
open scoped Topology
universe u
variable {Z : Type u} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]

noncomputable def measureOperator (ν : ProbabilityMeasure Z) : C(Z, ℂ) →L[ℂ] C(Z, ℂ) :=
  ambientOperator (ContinuousMap.id Z) (ν : Measure Z)

theorem measureOperator_integral (ν : ProbabilityMeasure Z) (f : C(Z, ℂ)) (z : Z) :
    measureOperator ν f z = ∫ y, (dist z y : ℂ) * f y ∂(ν : Measure Z) :=
  ambientOperator_integral (ContinuousMap.id Z) (ν : Measure Z) f z

theorem measureOperator_strong (νs : ℕ → ProbabilityMeasure Z) (ν : ProbabilityMeasure Z)
    (hν : Tendsto νs atTop (𝓝 ν)) (f : C(Z, ℂ)) :
    Tendsto (fun n ↦ measureOperator (νs n) f) atTop (𝓝 (measureOperator ν f)) := by
  let F : C(Z × Z, ℂ) := ⟨fun p ↦ (dist p.1 p.2 : ℂ) * f p.2, by fun_prop⟩
  have hu := PartI.parameterIntegrals_uniform νs ν hν (fun _ ↦ F) F (by simp)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hu (ε / 2) (half_pos hε)] with n hn
  rw [dist_eq_norm]
  apply lt_of_le_of_lt ((ContinuousMap.norm_le _ (by positivity : 0 ≤ ε/2)).mpr ?_)
    (by linarith : ε/2 < ε)
  intro z
  have hz := hn z
  simpa only [ContinuousMap.sub_apply, measureOperator_integral, F, ContinuousMap.coe_mk,
    dist_eq_norm, norm_sub_rev] using hz.le

/-- A single compact set contains the unit-ball images for every probability measure. -/
theorem measureOperator_collectivelyCompact :
    ∃ K : Set C(Z, ℂ), IsCompact K ∧
      ∀ (ν : ProbabilityMeasure Z) (f : C(Z, ℂ)), ‖f‖ ≤ 1 → measureOperator ν f ∈ K := by
  let E := ContinuousMap.linearIsometryBoundedOfCompact Z ℂ ℂ
  let S : Set (BoundedContinuousFunction Z ℂ) :=
    {g | ∃ ν : ProbabilityMeasure Z, ∃ f : C(Z, ℂ), ‖f‖ ≤ 1 ∧ E (measureOperator ν f) = g}
  have hc : IsCompact (closure S) := by
    apply BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) (diam (univ : Set Z)))
      (isCompact_closedBall _ _)
    · intro g z hg
      obtain ⟨ν, f, hf, rfl⟩ := hg
      have hr := (restriction_norm_le (ContinuousMap.id Z) (ν : Measure Z) f).trans hf
      rw [mem_closedBall, dist_eq_norm]
      change ‖distanceValue (ContinuousMap.id Z) (ν : Measure Z)
        (restriction (ContinuousMap.id Z) (ν : Measure Z) f) z - 0‖ ≤ _
      simpa using (distanceValue_bound (ContinuousMap.id Z) (ν : Measure Z) _ z).trans
        (mul_le_of_le_one_right diam_nonneg hr)
    · refine Metric.equicontinuous_of_continuity_modulus id continuous_id.continuousAt
        ((↑) : S → Z → ℂ) ?_
      intro z w g
      obtain ⟨ν, f, hf, he⟩ := g.property
      have hr := (restriction_norm_le (ContinuousMap.id Z) (ν : Measure Z) f).trans hf
      change dist (g.val z) (g.val w) ≤ dist z w
      rw [← he]
      exact (distanceValue_lipschitz (ContinuousMap.id Z) (ν : Measure Z)
        (restriction (ContinuousMap.id Z) (ν : Measure Z) f)).dist_le_mul z w |>.trans
          (by simpa using mul_le_of_le_one_left dist_nonneg hr)
  refine ⟨E.symm '' closure S, hc.image E.symm.continuous, ?_⟩
  intro ν f hf
  exact ⟨E (measureOperator ν f), subset_closure ⟨ν, f, hf, rfl⟩, E.symm_apply_apply _⟩

theorem measureOperator_differences_collectivelyCompact :
    ∃ K : Set C(Z, ℂ), IsCompact K ∧
      ∀ (ν μ : ProbabilityMeasure Z) (f : C(Z, ℂ)), ‖f‖ ≤ 1 →
        measureOperator ν f - measureOperator μ f ∈ K := by
  obtain ⟨K, hK, hmem⟩ := measureOperator_collectivelyCompact (Z := Z)
  refine ⟨(fun p : C(Z, ℂ) × C(Z, ℂ) ↦ p.1 - p.2) '' (K ×ˢ K),
    (hK.prod hK).image (continuous_fst.sub continuous_snd), ?_⟩
  intro ν μ f hf
  exact ⟨(measureOperator ν f, measureOperator μ f), ⟨hmem ν f hf, hmem μ f hf⟩, rfl⟩

universe v
variable {X : Type v} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

theorem ambientOperator_eq_measureOperator (e : C(X, Z)) (μ : ProbabilityMeasure X) :
    ambientOperator e (μ : Measure X) = measureOperator (μ.map e) := by
  apply ContinuousLinearMap.ext
  intro f
  ext z
  rw [ambientOperator_integral, measureOperator_integral, ProbabilityMeasure.toMeasure_map]
  symm
  exact integral_map e.continuous.measurable.aemeasurable
    (show Continuous (fun y : Z ↦ (dist z y : ℂ) * f y) by fun_prop).aestronglyMeasurable

theorem ambientOperator_strong_of_pushforward
    {Xs : ℕ → Type v} [∀ n, MetricSpace (Xs n)] [∀ n, CompactSpace (Xs n)]
    [∀ n, MeasurableSpace (Xs n)] [∀ n, BorelSpace (Xs n)]
    (es : ∀ n, C(Xs n, Z)) (μs : ∀ n, ProbabilityMeasure (Xs n))
    (e : C(X, Z)) (μ : ProbabilityMeasure X)
    (hμ : Tendsto (fun n ↦ (μs n).map (es n)) atTop
      (𝓝 (μ.map e))) (f : C(Z, ℂ)) :
    Tendsto (fun n ↦ ambientOperator (es n) (μs n : Measure (Xs n)) f) atTop
      (𝓝 (ambientOperator e (μ : Measure X) f)) := by
  simp_rw [ambientOperator_eq_measureOperator]
  exact measureOperator_strong _ _ hμ f

theorem ambientOperator_collectivelyCompact
    {Xs : ℕ → Type v} [∀ n, MetricSpace (Xs n)] [∀ n, CompactSpace (Xs n)]
    [∀ n, MeasurableSpace (Xs n)] [∀ n, BorelSpace (Xs n)]
    (es : ∀ n, C(Xs n, Z)) (μs : ∀ n, ProbabilityMeasure (Xs n)) :
    ∃ K : Set C(Z, ℂ), IsCompact K ∧
      ∀ n (f : C(Z, ℂ)), ‖f‖ ≤ 1 → ambientOperator (es n) (μs n : Measure (Xs n)) f ∈ K := by
  obtain ⟨K, hK, hm⟩ := measureOperator_collectivelyCompact (Z := Z)
  refine ⟨K, hK, ?_⟩
  intro n f hf
  rw [ambientOperator_eq_measureOperator]
  exact hm _ f hf

end PaperN.PartII.AmbientKernel
