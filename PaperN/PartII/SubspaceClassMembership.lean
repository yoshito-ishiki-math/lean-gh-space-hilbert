import PaperN.PartII.SelectedSpectralBasis
import PaperN.PartII.SubspaceCoordinateClass
import PaperN.PartII.CoordinateClassRepair

namespace PaperN.PartII
open MeasureTheory Filter Topology
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
  (S : Submodule ℝ C(X, ℝ)) [FiniteDimensional ℝ S]
  (p : ENNReal) [Fact (1 ≤ p)] [StrictConvexSpace ℝ (Lp ℝ p μ)]

/-- A full orthonormal family gives an actual representative with exactly the
raw minimizer coordinates and the prescribed coordinate norm. -/
theorem exists_subspace_class_representative
    (n : ℕ) (hn : n = Module.finrank ℝ S) (v : Fin n → C(X, ℝ))
    (hmem : ∀ i, v i ∈ S) (ho : Orthonormal ℝ (fun i ↦ continuousToL2 μ (v i))) :
    ∃ a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin n)),
      Quotient.mk _ a = subspaceCoordinateClass μ S p n hn ∧
      (⇑a.coordinates = fun x ↦ coordinateLpMinimizer μ p v
        (ContinuousMap.toLp p μ ℝ (distanceProfile x))) ∧
      a.norm = coordinateLpNorm μ p v := by
  let w : Fin n → S := fun i ↦ ⟨v i, hmem i⟩
  have hi : LinearIndependent ℝ v :=
    LinearIndependent.of_comp (continuousToL2 μ).toLinearMap ho.linearIndependent
  refine ⟨bestApproximationCoordinatePair μ p v hi, ?_, rfl, rfl⟩
  exact (subspaceCoordinateClass_eq_of_orthonormal_family μ S p n hn w ho hi).symm

end PaperN.PartII

namespace PaperN.PartII
open MeasureTheory Filter Topology

/-- Eventually full orthonormal candidate families can be completed to class
representatives at every index, preserving the entire tail of raw data. -/
theorem repair_subspace_class_families
    (Xs : ℕ → Type*) [∀ k, MetricSpace (Xs k)] [∀ k, CompactSpace (Xs k)]
    [∀ k, MeasurableSpace (Xs k)] [∀ k, BorelSpace (Xs k)]
    (μs : ∀ k, ProbabilityMeasure (Xs k)) [∀ k, (μs k : Measure (Xs k)).IsOpenPosMeasure]
    (S : ∀ k, Submodule ℝ C(Xs k, ℝ)) [∀ k, FiniteDimensional ℝ (S k)]
    (p : ENNReal) [Fact (1 ≤ p)] [∀ k, StrictConvexSpace ℝ (Lp ℝ p (μs k : Measure (Xs k)))]
    (n : ℕ) (hd : ∀ k, n = Module.finrank ℝ (S k))
    (vs : ∀ k, Fin n → C(Xs k, ℝ))
    (hv : ∀ᶠ k in atTop, (∀ i, vs k i ∈ S k) ∧
      Orthonormal ℝ (fun i ↦ continuousToL2 (μs k : Measure (Xs k)) (vs k i))) :
    ∃ as : ∀ k, NormedCoordinatePair (Xs k) (EuclideanSpace ℝ (Fin n)),
      (∀ k, Quotient.mk _ (as k) = subspaceCoordinateClass (μs k : Measure (Xs k))
        (S k) p n (hd k)) ∧
      ∀ᶠ k in atTop,
        (⇑(as k).coordinates = fun x ↦ coordinateLpMinimizer (μs k : Measure (Xs k)) p
          (vs k) (ContinuousMap.toLp p (μs k : Measure (Xs k)) ℝ (distanceProfile x))) ∧
        (as k).norm = coordinateLpNorm (μs k : Measure (Xs k)) p (vs k) := by
  apply repair_coordinate_class_representatives Xs
  filter_upwards [hv] with k hk
  exact exists_subspace_class_representative (μs k : Measure (Xs k)) (S k) p n
    (hd k) (vs k) hk.1 hk.2

end PaperN.PartII

namespace PaperN.PartII
open MeasureTheory Filter Topology

/-- Positive spectral cutoffs supply the finite-dimensionality needed by the
actual class-membership construction. -/
theorem exists_spectral_class_representative
    (hf : CompactEigenvalueFinitenessInput.{0})
    (X : Type) [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (η : ℝ) (hη : 0 < η) (p : ENNReal) [Fact (1 ≤ p)]
    [StrictConvexSpace ℝ (Lp ℝ p μ)]
    (n : ℕ) (hn : n = Module.finrank ℝ (spectralCutoff μ η))
    (v : Fin n → C(X, ℝ)) (hv : ∀ i, v i ∈ spectralCutoff μ η)
    (ho : Orthonormal ℝ (fun i ↦ continuousToL2 μ (v i))) :
    ∃ hfin : FiniteDimensional ℝ (spectralCutoff μ η),
      ∃ a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin n)),
        Quotient.mk _ a = @subspaceCoordinateClass X _ _ _ _ μ _ _
          (spectralCutoff μ η) hfin p _ _ n hn ∧
        (⇑a.coordinates = fun x ↦ coordinateLpMinimizer μ p v
          (ContinuousMap.toLp p μ ℝ (distanceProfile x))) ∧
        a.norm = coordinateLpNorm μ p v := by
  letI := ComplexKernel.realCutoff_finiteDimensional μ hf η hη
  letI : FiniteDimensional ℝ (spectralCutoff μ η) :=
    (spectralCutoffEquiv μ hη).symm.finiteDimensional
  exact ⟨inferInstance, exists_subspace_class_representative μ (spectralCutoff μ η) p n hn v hv ho⟩

end PaperN.PartII
