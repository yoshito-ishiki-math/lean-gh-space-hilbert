import PaperN.PartII.ContinuousOrthonormalBasis

namespace PaperN.PartII
open MeasureTheory
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
  (S : Submodule ℝ C(X, ℝ)) [FiniteDimensional ℝ S]

/-- A prescribed dimension equal to the rank admits an L2 orthonormal continuous basis. -/
theorem exists_continuous_orthonormal_basis_fin (n : ℕ) (hn : n = Module.finrank ℝ S) :
    ∃ b : Module.Basis (Fin n) ℝ S,
      Orthonormal ℝ (fun i ↦ continuousToL2 μ (b i)) := by
  obtain ⟨m, b, hm, ho⟩ := exists_continuous_orthonormal_basis μ S
  have hmn : m = n := hm.trans hn.symm
  cases hmn
  exact ⟨b, ho⟩

noncomputable def subspaceOrthonormalBasis (n : ℕ) (hn : n = Module.finrank ℝ S) :
    Module.Basis (Fin n) ℝ S :=
  (exists_continuous_orthonormal_basis_fin μ S n hn).choose

theorem subspaceOrthonormalBasis_orthonormal (n : ℕ) (hn : n = Module.finrank ℝ S) :
    Orthonormal ℝ (fun i ↦ continuousToL2 μ (subspaceOrthonormalBasis μ S n hn i)) :=
  (exists_continuous_orthonormal_basis_fin μ S n hn).choose_spec

variable (p : ENNReal) [Fact (1 ≤ p)] [StrictConvexSpace ℝ (Lp ℝ p μ)]

/-- The coordinate class of a finite continuous subspace, using its L2 geometry. -/
noncomputable def subspaceCoordinateClass (n : ℕ) (hn : n = Module.finrank ℝ S) :
    NormedCoordinateClass X (EuclideanSpace ℝ (Fin n)) :=
  Quotient.mk _ (bestApproximationCoordinatePair μ p
    (fun i ↦ (subspaceOrthonormalBasis μ S n hn i : C(X, ℝ)))
    (LinearIndependent.of_comp (continuousToL2 μ).toLinearMap
      (subspaceOrthonormalBasis_orthonormal μ S n hn).linearIndependent))

/-- Every full orthonormal family represents the same subspace coordinate class. -/
theorem subspaceCoordinateClass_eq_of_orthonormal_family
    (n : ℕ) (hn : n = Module.finrank ℝ S) (v : Fin n → S)
    (ho : Orthonormal ℝ (fun i ↦ continuousToL2 μ (v i)))
    (hli : LinearIndependent ℝ (fun i ↦ (v i : C(X, ℝ)))) :
    subspaceCoordinateClass μ S p n hn =
      Quotient.mk _ (bestApproximationCoordinatePair μ p (fun i ↦ (v i : C(X, ℝ))) hli) := by
  obtain ⟨hi, hj, h⟩ := coordinate_class_independent_of_full_orthonormal_family μ S p
    (subspaceOrthonormalBasis μ S n hn) v
    (subspaceOrthonormalBasis_orthonormal μ S n hn) ho (by simpa using hn)
  exact h

end PaperN.PartII
