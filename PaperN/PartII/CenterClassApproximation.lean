import PaperN.PartII.CenterApproximation
import PaperN.PartII.SubspaceModelBounds

namespace PaperN.PartII.AmbientKernel
open MeasureTheory Metric Set PaperN.PartI

/-- The center approximation holds for every representative of the selected
spectral coordinate class, not only for the pair used to prove existence. -/
theorem exists_center_class_approximation
    (hm : GHPMetricInput.{0}) (hs : InvariantFiberLawSelectionStatement hm)
    (hk : DistanceKernelSpectralInput.{0}) (hf : CompactEigenvalueFinitenessInput.{0})
    (X : MeasuredCompact.{0}) (τ : ℝ) (hτ : 0 < τ) :
    ∃ q η : ℝ, 2 ≤ q ∧ ∃ hη : 0 < η,
      (η : ℂ) ∉ complexifiedSpectrum (distanceOperator (selectedProbability hm hs X : Measure X)) ∧
      ((-η : ℝ) : ℂ) ∉ complexifiedSpectrum (distanceOperator (selectedProbability hm hs X : Measure X)) ∧
      ∃ n : ℕ, ∃ hn : n = Module.finrank ℝ
        (spectralCutoff (selectedProbability hm hs X : Measure X) η),
        (Nontrivial X → 0 < n) ∧
        ∀ [Fact (1 ≤ ENNReal.ofReal q)]
          [StrictConvexSpace ℝ (Lp ℝ (ENNReal.ofReal q) (selectedProbability hm hs X : Measure X))]
          (a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin n))),
          Quotient.mk _ a = selectedSpectralCoordinateClass hm hs hf X η hη (ENNReal.ofReal q) n hn →
          (∀ x : X, a.norm (a.coordinates x) ≤ 2 * diam (univ : Set X)) ∧
          (⨆ z : X × X, |a.pseudometric z.1 z.2 - dist z.1 z.2|) < τ := by
  let μ := selectedProbability hm hs X
  letI : (μ : Measure X).IsOpenPosMeasure :=
    openPos_of_support_eq_univ _ (selectedProbability_fullSupport_invariant hm hs X).1
  obtain ⟨q, η, hq, hη, hp, hn, hfin, hdim, herr⟩ :=
    exists_center_approximation_parameters hk hf X (μ : Measure X) τ hτ
  letI := hfin
  let S := spectralCutoff (μ : Measure X) η
  let n := Module.finrank ℝ S
  refine ⟨q, η, hq, hη, hp, hn, n, rfl, hdim, ?_⟩
  intro _ _ a ha
  have ha' : Quotient.mk _ a = subspaceCoordinateClass (μ : Measure X) S (ENNReal.ofReal q) n rfl := ha
  refine ⟨fun x ↦ subspaceCoordinateClass_representative_bound
    (μ : Measure X) S (ENNReal.ofReal q) n rfl a ha' x, ?_⟩
  let b := subspaceOrthonormalBasis (μ : Measure X) S n rfl
  have hi : LinearIndependent ℝ (fun i ↦ (b i : C(X, ℝ))) :=
    LinearIndependent.of_comp (continuousToL2 (μ : Measure X)).toLinearMap
      (subspaceOrthonormalBasis_orthonormal (μ : Measure X) S n rfl).linearIndependent
  have heq : a.pseudometric =
      (bestApproximationCoordinatePair (μ : Measure X) (ENNReal.ofReal q)
        (fun i ↦ (b i : C(X, ℝ))) hi).pseudometric :=
    congrArg (NormedCoordinateClass.pseudometric X (EuclideanSpace ℝ (Fin n))) ha'
  rw [heq]
  exact herr n b hi

end PaperN.PartII.AmbientKernel
