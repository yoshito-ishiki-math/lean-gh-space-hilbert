import PaperN.PartII.BestApproximationNaturality

namespace PaperN.PartII
open MeasureTheory
variable {X ι : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Fintype ι]
  (μ : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- Coordinates from one orthonormal basis to another. -/
noncomputable def orthonormalCoordinateChange (S : Submodule ℝ (Lp ℝ 2 μ))
    (b c : OrthonormalBasis ι ℝ S) : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
  b.repr.symm.trans c.repr

omit [μ.IsOpenPosMeasure] in
theorem synthesis_toLp_basis (S : Submodule ℝ (Lp ℝ 2 μ))
    (b : OrthonormalBasis ι ℝ S) (v : ι → C(X, ℝ))
    (hv : ∀ i, ContinuousMap.toLp 2 μ ℝ (v i) = (b i : Lp ℝ 2 μ))
    (a : EuclideanSpace ℝ ι) :
    coordinateLpMap μ 2 v a = (b.repr.symm a : Lp ℝ 2 μ) := by
  classical
  change ContinuousMap.toLp 2 μ ℝ (∑ i, a i • v i) = _
  simp only [map_sum, map_smul, hv]
  rw [← b.sum_repr_symm]
  simp

theorem coordinateSynthesis_change_basis (S : Submodule ℝ (Lp ℝ 2 μ))
    (b c : OrthonormalBasis ι ℝ S) (v w : ι → C(X, ℝ))
    (hv : ∀ i, ContinuousMap.toLp 2 μ ℝ (v i) = (b i : Lp ℝ 2 μ))
    (hw : ∀ i, ContinuousMap.toLp 2 μ ℝ (w i) = (c i : Lp ℝ 2 μ))
    (a : EuclideanSpace ℝ ι) :
    coordinateSynthesis w (orthonormalCoordinateChange μ S b c a) = coordinateSynthesis v a := by
  apply ContinuousMap.toLp_injective μ (p := 2) (𝕜 := ℝ)
  change coordinateLpMap μ 2 w _ = coordinateLpMap μ 2 v a
  rw [synthesis_toLp_basis μ S c w hw, synthesis_toLp_basis μ S b v hv]
  simp [orthonormalCoordinateChange]

theorem coordinateLpMap_change_orthonormal_basis (p : ENNReal) [Fact (1 ≤ p)]
    (S : Submodule ℝ (Lp ℝ 2 μ)) (b c : OrthonormalBasis ι ℝ S)
    (v w : ι → C(X, ℝ))
    (hv : ∀ i, ContinuousMap.toLp 2 μ ℝ (v i) = (b i : Lp ℝ 2 μ))
    (hw : ∀ i, ContinuousMap.toLp 2 μ ℝ (w i) = (c i : Lp ℝ 2 μ))
    (a : EuclideanSpace ℝ ι) :
    coordinateLpMap μ p w (orthonormalCoordinateChange μ S b c a) = coordinateLpMap μ p v a := by
  change ContinuousMap.toLp p μ ℝ _ = ContinuousMap.toLp p μ ℝ _
  rw [coordinateSynthesis_change_basis μ S b c v w hv hw]

end PaperN.PartII

namespace PaperN.PartII
open MeasureTheory
variable {X ι : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Fintype ι]
  (μ : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
  (p : ENNReal) [Fact (1 ≤ p)] [StrictConvexSpace ℝ (Lp ℝ p μ)]

theorem bestApproximationCoordinatePair_class_eq_of_orthonormal_bases
    (S : Submodule ℝ (Lp ℝ 2 μ)) (b c : OrthonormalBasis ι ℝ S)
    (v w : ι → C(X, ℝ)) (hvli : LinearIndependent ℝ v) (hwli : LinearIndependent ℝ w)
    (hv : ∀ i, ContinuousMap.toLp 2 μ ℝ (v i) = (b i : Lp ℝ 2 μ))
    (hw : ∀ i, ContinuousMap.toLp 2 μ ℝ (w i) = (c i : Lp ℝ 2 μ)) :
    (Quotient.mk _ (bestApproximationCoordinatePair μ p v hvli) :
      NormedCoordinateClass X (EuclideanSpace ℝ ι)) =
      Quotient.mk _ (bestApproximationCoordinatePair μ p w hwli) :=
  bestApproximationCoordinatePair_class_eq μ p v w hvli hwli
    (orthonormalCoordinateChange μ S b c)
    (coordinateLpMap_change_orthonormal_basis μ p S b c v w hv hw)

end PaperN.PartII
