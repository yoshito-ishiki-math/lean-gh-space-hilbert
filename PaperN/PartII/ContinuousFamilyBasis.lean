import PaperN.PartII.OrthonormalCoordinateChange
import PaperN.PartII.GramRestriction

namespace PaperN.PartII
open MeasureTheory
variable {X ι : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Fintype ι] [DecidableEq ι]
  (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
  (S : Submodule ℝ C(X, ℝ)) [FiniteDimensional ℝ S]

noncomputable def continuousSubspaceL2Map : S →ₗ[ℝ] Lp ℝ 2 μ :=
  (continuousToL2 μ).toLinearMap.comp S.subtype

noncomputable def continuousSubspaceL2Equiv :
    S ≃ₗ[ℝ] (continuousSubspaceL2Map μ S).range :=
  LinearEquiv.ofInjective (continuousSubspaceL2Map μ S)
    ((ContinuousMap.toLp_injective μ).comp Subtype.val_injective)

noncomputable def continuousFamilyL2 (v : ι → S) : ι → (continuousSubspaceL2Map μ S).range :=
  fun i ↦ continuousSubspaceL2Equiv μ S (v i)

omit [Fintype ι] [FiniteDimensional ℝ S] in
theorem continuousFamilyL2_orthonormal (v : ι → S)
    (hv : Orthonormal ℝ (fun i ↦ continuousToL2 μ (v i))) :
    Orthonormal ℝ (continuousFamilyL2 μ S v) := by
  rw [orthonormal_iff_ite] at hv ⊢
  exact hv

noncomputable def continuousFamilyOrthonormalBasis (v : ι → S)
    (hv : Orthonormal ℝ (fun i ↦ continuousToL2 μ (v i)))
    (hd : Fintype.card ι = Module.finrank ℝ S) :
    OrthonormalBasis ι ℝ (continuousSubspaceL2Map μ S).range := by
  have ho := continuousFamilyL2_orthonormal μ S v hv
  have hd' : Fintype.card ι = Module.finrank ℝ (continuousSubspaceL2Map μ S).range :=
    hd.trans (continuousSubspaceL2Equiv μ S).finrank_eq
  exact OrthonormalBasis.mk ho (by rw [ho.linearIndependent.span_eq_top_of_card_eq_finrank' hd'])

theorem continuousFamilyOrthonormalBasis_apply (v : ι → S)
    (hv : Orthonormal ℝ (fun i ↦ continuousToL2 μ (v i)))
    (hd : Fintype.card ι = Module.finrank ℝ S) (i : ι) :
    (continuousFamilyOrthonormalBasis μ S v hv hd i : Lp ℝ 2 μ) = continuousToL2 μ (v i) := by
  unfold continuousFamilyOrthonormalBasis
  change Subtype.val ((⇑(OrthonormalBasis.mk _ _)) i) = _
  rw [OrthonormalBasis.coe_mk]
  rfl

end PaperN.PartII

namespace PaperN.PartII
open MeasureTheory
variable {X ι : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Fintype ι] [DecidableEq ι]
  (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
  (S : Submodule ℝ C(X, ℝ)) [FiniteDimensional ℝ S]
  (p : ENNReal) [Fact (1 ≤ p)] [StrictConvexSpace ℝ (Lp ℝ p μ)]

theorem coordinate_class_independent_of_full_orthonormal_family
    (v w : ι → S)
    (hv : Orthonormal ℝ (fun i ↦ continuousToL2 μ (v i)))
    (hw : Orthonormal ℝ (fun i ↦ continuousToL2 μ (w i)))
    (hd : Fintype.card ι = Module.finrank ℝ S) :
    ∃ hvli : LinearIndependent ℝ (fun i ↦ (v i : C(X, ℝ))),
    ∃ hwli : LinearIndependent ℝ (fun i ↦ (w i : C(X, ℝ))),
    (Quotient.mk _ (bestApproximationCoordinatePair μ p (fun i ↦ (v i : C(X, ℝ))) hvli) :
      NormedCoordinateClass X (EuclideanSpace ℝ ι)) =
      Quotient.mk _ (bestApproximationCoordinatePair μ p (fun i ↦ (w i : C(X, ℝ))) hwli) := by
  have hvli : LinearIndependent ℝ (fun i ↦ (v i : C(X, ℝ))) :=
    LinearIndependent.of_comp (continuousToL2 μ).toLinearMap hv.linearIndependent
  have hwli : LinearIndependent ℝ (fun i ↦ (w i : C(X, ℝ))) :=
    LinearIndependent.of_comp (continuousToL2 μ).toLinearMap hw.linearIndependent
  refine ⟨hvli, hwli, ?_⟩
  apply bestApproximationCoordinatePair_class_eq_of_orthonormal_bases μ p
    (continuousSubspaceL2Map μ S).range
    (continuousFamilyOrthonormalBasis μ S v hv hd)
    (continuousFamilyOrthonormalBasis μ S w hw hd)
  · intro i
    exact (continuousFamilyOrthonormalBasis_apply μ S v hv hd i).symm
  · intro i
    exact (continuousFamilyOrthonormalBasis_apply μ S w hw hd i).symm

end PaperN.PartII
