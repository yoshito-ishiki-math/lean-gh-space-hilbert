import PaperN.PartII.CenterClassApproximation
import PaperN.PartII.ComplexificationResolvent

namespace PaperN.PartII.AmbientKernel
open MeasureTheory Metric Set PaperN.PartI

/-- The center parameters satisfy the actual complex L2 resolvent hypotheses
used to construct the spectral neighborhood. -/
theorem exists_center_class_approximation_resolvent
    (hm : GHPMetricInput.{0}) (hs : InvariantFiberLawSelectionStatement hm)
    (hk : DistanceKernelSpectralInput.{0}) (hf : CompactEigenvalueFinitenessInput.{0})
    (X : MeasuredCompact.{0}) (τ : ℝ) (hτ : 0 < τ) :
    ∃ q η : ℝ, 2 ≤ q ∧ ∃ hη : 0 < η,
      (η : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator (selectedProbability hm hs X : Measure X)) ∧
      ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator (selectedProbability hm hs X : Measure X)) ∧
      ∃ n : ℕ, ∃ hn : n = Module.finrank ℝ
        (spectralCutoff (selectedProbability hm hs X : Measure X) η),
        (Nontrivial X → 0 < n) ∧
        ∀ [Fact (1 ≤ ENNReal.ofReal q)]
          [StrictConvexSpace ℝ (Lp ℝ (ENNReal.ofReal q) (selectedProbability hm hs X : Measure X))]
          (a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin n))),
          Quotient.mk _ a = selectedSpectralCoordinateClass hm hs hf X η hη (ENNReal.ofReal q) n hn →
          (∀ x : X, a.norm (a.coordinates x) ≤ 2 * diam (univ : Set X)) ∧
          (⨆ z : X × X, |a.pseudometric z.1 z.2 - dist z.1 z.2|) < τ := by
  obtain ⟨q, η, hq, hη, hp, hn, n, hdim, hnontrivial, herr⟩ :=
    exists_center_class_approximation hm hs hk hf X τ hτ
  refine ⟨q, η, hq, hη, ?_, ?_, n, hdim, hnontrivial, herr⟩
  · exact ComplexKernel.ofReal_mem_resolventSet_of_not_mem_complexifiedSpectrum
      (selectedProbability hm hs X : Measure X) η (ne_of_gt hη) hp
  · exact ComplexKernel.ofReal_mem_resolventSet_of_not_mem_complexifiedSpectrum
      (selectedProbability hm hs X : Measure X) (-η) (neg_ne_zero.mpr (ne_of_gt hη)) hn

end PaperN.PartII.AmbientKernel
