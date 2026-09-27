import PaperN.PartII.SubspaceClassPullback

namespace PaperN.PartII
open MeasureTheory
variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem distanceToContinuous_toL2_integral (μ : ProbabilityMeasure X) (f : C(X, ℝ)) (x : X) :
    distanceToContinuous (μ : Measure X) (continuousToL2 (μ : Measure X) f) x =
      ∫ y, dist x y * f y ∂(μ : Measure X) := by
  exact distanceValue_integral_of_ae (μ : Measure X) _ f
    (f.coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure X)).symm x

/-- The continuous representative of the distance operator commutes with pullback. -/
theorem distanceToContinuous_toL2_comap
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (e : X → Y) (he : Isometry e) (hμ : μ.map he.continuous.measurable.aemeasurable = ν)
    (f : C(Y, ℝ)) :
    (distanceToContinuous (ν : Measure Y) (continuousToL2 (ν : Measure Y) f)).comp
      ⟨e, he.continuous⟩ =
    distanceToContinuous (μ : Measure X)
      (continuousToL2 (μ : Measure X) (f.comp ⟨e, he.continuous⟩)) := by
  ext x
  change distanceToContinuous (ν : Measure Y) (continuousToL2 (ν : Measure Y) f) (e x) = _
  rw [distanceToContinuous_toL2_integral, distanceToContinuous_toL2_integral, ← hμ,
    ProbabilityMeasure.toMeasure_map]
  rw [integral_map he.continuous.measurable.aemeasurable]
  · simp only [he.dist_eq, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  · exact ((continuous_const.dist continuous_id).mul f.continuous).aestronglyMeasurable

/-- Continuous eigenfunctions pull back to eigenfunctions with the same eigenvalue. -/
theorem continuousEigenfunction_comap
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) [(ν : Measure Y).IsOpenPosMeasure]
    (e : X → Y) (he : Isometry e) (hμ : μ.map he.continuous.measurable.aemeasurable = ν)
    (f : C(Y, ℝ)) (a : ℝ)
    (hf : distanceOperator (ν : Measure Y) (continuousToL2 (ν : Measure Y) f) =
      a • continuousToL2 (ν : Measure Y) f) :
    distanceOperator (μ : Measure X)
      (continuousToL2 (μ : Measure X) (f.comp ⟨e, he.continuous⟩)) =
      a • continuousToL2 (μ : Measure X) (f.comp ⟨e, he.continuous⟩) := by
  have hcont : distanceToContinuous (ν : Measure Y) (continuousToL2 (ν : Measure Y) f) = a • f := by
    apply continuousToL2_injective (ν : Measure Y)
    simpa [distanceOperator] using hf
  have h := congrArg (fun g : C(Y, ℝ) ↦ g.comp ⟨e, he.continuous⟩) hcont
  rw [distanceToContinuous_toL2_comap μ ν e he hμ] at h
  have hh := congrArg (continuousToL2 (μ : Measure X)) h
  simpa [distanceOperator, ContinuousMap.smul_comp] using hh

/-- The entire algebraic continuous cutoff is preserved by isometric pullback. -/
theorem spectralCutoff_comap_mem
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) [(ν : Measure Y).IsOpenPosMeasure]
    (e : X → Y) (he : Isometry e) (hμ : μ.map he.continuous.measurable.aemeasurable = ν)
    (η : ℝ) (f : C(Y, ℝ)) (hf : f ∈ spectralCutoff (ν : Measure Y) η) :
    f.comp ⟨e, he.continuous⟩ ∈ spectralCutoff (μ : Measure X) η := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ha, heigen⟩ := hf
    exact Submodule.subset_span ⟨a, ha, continuousEigenfunction_comap μ ν e he hμ f a heigen⟩
  | zero => exact (spectralCutoff (μ : Measure X) η).zero_mem
  | add f g hf hg ihf ihg => exact (spectralCutoff (μ : Measure X) η).add_mem ihf ihg
  | smul a f hf ih => exact (spectralCutoff (μ : Measure X) η).smul_mem a ih

end PaperN.PartII
