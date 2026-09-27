import PaperN.PartII.SpectralCutoffPullback
import PaperN.PartII.SelectedClassConvergence

namespace PaperN.PartII
open MeasureTheory
variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

omit [CompactSpace X] [CompactSpace Y] in
theorem probability_map_isometryEquiv_symm (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (e : X ≃ᵢ Y) (hμ : μ.map e.continuous.measurable.aemeasurable = ν) :
    ν.map e.symm.continuous.measurable.aemeasurable = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map, ← hμ, ProbabilityMeasure.toMeasure_map,
    Measure.map_map e.symm.continuous.measurable e.continuous.measurable]
  have he : (e.symm : Y → X) ∘ e = id := by
    funext x
    exact e.symm_apply_apply x
  rw [he, Measure.map_id]

/-- Both directions of pullback give a linear equivalence of full spectral cutoffs. -/
noncomputable def spectralCutoffPullbackEquiv
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    [(μ : Measure X).IsOpenPosMeasure] [(ν : Measure Y).IsOpenPosMeasure]
    (e : X ≃ᵢ Y) (hμ : μ.map e.continuous.measurable.aemeasurable = ν) (η : ℝ) :
    spectralCutoff (ν : Measure Y) η ≃ₗ[ℝ] spectralCutoff (μ : Measure X) η where
  toFun f := ⟨(f : C(Y, ℝ)).comp ⟨e, e.continuous⟩,
    spectralCutoff_comap_mem μ ν e e.isometry hμ η f f.property⟩
  invFun f := ⟨(f : C(X, ℝ)).comp ⟨e.symm, e.symm.continuous⟩,
    spectralCutoff_comap_mem ν μ e.symm e.symm.isometry
      (probability_map_isometryEquiv_symm μ ν e hμ) η f f.property⟩
  left_inv := by
    intro f
    apply Subtype.ext
    ext y
    simp
  right_inv := by
    intro f
    apply Subtype.ext
    ext x
    simp
  map_add' := by
    intro f g
    rfl
  map_smul' := by
    intro a f
    rfl

theorem spectralCutoff_finrank_eq_of_isometryEquiv
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    [(μ : Measure X).IsOpenPosMeasure] [(ν : Measure Y).IsOpenPosMeasure]
    (e : X ≃ᵢ Y) (hμ : μ.map e.continuous.measurable.aemeasurable = ν) (η : ℝ) :
    Module.finrank ℝ (spectralCutoff (μ : Measure X) η) =
      Module.finrank ℝ (spectralCutoff (ν : Measure Y) η) :=
  (spectralCutoffPullbackEquiv μ ν e hμ η).finrank_eq.symm

namespace AmbientKernel
open PaperN.PartI ComplexKernel

/-- Selected spectral coordinate classes are natural under whole-carrier isometries. -/
theorem selectedSpectralCoordinateClass_comap
    (hm : GHPMetricInput.{0}) (hs : InvariantFiberLawSelectionStatement hm)
    (hf : CompactEigenvalueFinitenessInput.{0}) (X Y : MeasuredCompact.{0})
    (e : X ≃ᵢ Y) (η : ℝ) (hη : 0 < η) (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs X : Measure X))]
    [StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs Y : Measure Y))]
    (n : ℕ)
    (hX : n = Module.finrank ℝ (spectralCutoff (selectedProbability hm hs X : Measure X) η))
    (hY : n = Module.finrank ℝ (spectralCutoff (selectedProbability hm hs Y : Measure Y) η)) :
    (selectedSpectralCoordinateClass hm hs hf Y η hη p n hY).comap ⟨e, e.continuous⟩ =
      selectedSpectralCoordinateClass hm hs hf X η hη p n hX := by
  let μ := selectedProbability hm hs X
  let ν := selectedProbability hm hs Y
  letI : (μ : Measure X).IsOpenPosMeasure :=
    openPos_of_support_eq_univ _ (selectedProbability_fullSupport_invariant hm hs X).1
  letI : (ν : Measure Y).IsOpenPosMeasure :=
    openPos_of_support_eq_univ _ (selectedProbability_fullSupport_invariant hm hs Y).1
  letI := realCutoff_finiteDimensional (μ : Measure X) hf η hη
  letI := realCutoff_finiteDimensional (ν : Measure Y) hf η hη
  letI : FiniteDimensional ℝ (spectralCutoff (μ : Measure X) η) :=
    (spectralCutoffEquiv (μ : Measure X) hη).symm.finiteDimensional
  letI : FiniteDimensional ℝ (spectralCutoff (ν : Measure Y) η) :=
    (spectralCutoffEquiv (ν : Measure Y) hη).symm.finiteDimensional
  have hμ := selectedProbability_natural hm hs X Y e
  exact subspaceCoordinateClass_comap μ ν _ _ e e.isometry hμ
    (fun f hf ↦ spectralCutoff_comap_mem μ ν e e.isometry hμ η f hf) p hp n hX hY

end AmbientKernel
end PaperN.PartII
