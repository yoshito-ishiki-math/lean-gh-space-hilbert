import PaperN.PartII.BestApproximationPullback
import PaperN.PartII.SubspaceCoordinateClass
import PaperN.PartII.GramRestriction

namespace PaperN.PartII
open MeasureTheory
variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- A continuous measure pushforward preserves orthonormality of pulled-back families. -/
theorem orthonormal_continuousFamily_comap {ι : Type*} [DecidableEq ι]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) (e : C(X, Y))
    (hμ : μ.map e.continuous.measurable.aemeasurable = ν) (v : ι → C(Y, ℝ))
    (ho : Orthonormal ℝ (fun i ↦ continuousToL2 (ν : Measure Y) (v i))) :
    Orthonormal ℝ (fun i ↦ continuousToL2 (μ : Measure X) ((v i).comp e)) := by
  apply (continuousGram_eq_one_iff μ _).mp
  rw [← continuousGram_map, hμ]
  exact (continuousGram_eq_one_iff ν v).mpr ho

/-- Equal-rank subspaces compatible with an isometric measure pushforward have
compatible coordinate classes; no agreement of the chosen bases is required. -/
theorem subspaceCoordinateClass_comap
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    [(μ : Measure X).IsOpenPosMeasure] [(ν : Measure Y).IsOpenPosMeasure]
    (S : Submodule ℝ C(X, ℝ)) (T : Submodule ℝ C(Y, ℝ))
    [FiniteDimensional ℝ S] [FiniteDimensional ℝ T]
    (e : X → Y) (he : Isometry e) (hμ : μ.map he.continuous.measurable.aemeasurable = ν)
    (hST : ∀ f ∈ T, f.comp ⟨e, he.continuous⟩ ∈ S)
    (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [StrictConvexSpace ℝ (Lp ℝ p (μ : Measure X))]
    [StrictConvexSpace ℝ (Lp ℝ p (ν : Measure Y))]
    (n : ℕ) (hS : n = Module.finrank ℝ S) (hT : n = Module.finrank ℝ T) :
    (subspaceCoordinateClass (ν : Measure Y) T p n hT).comap ⟨e, he.continuous⟩ =
      subspaceCoordinateClass (μ : Measure X) S p n hS := by
  let b := subspaceOrthonormalBasis (ν : Measure Y) T n hT
  let v := fun i ↦ (b i : C(Y, ℝ))
  have ho := subspaceOrthonormalBasis_orthonormal (ν : Measure Y) T n hT
  have hve := orthonormal_continuousFamily_comap μ ν ⟨e, he.continuous⟩ hμ v ho
  have hi : LinearIndependent ℝ v :=
    LinearIndependent.of_comp (continuousToL2 (ν : Measure Y)).toLinearMap ho.linearIndependent
  have hie : LinearIndependent ℝ (fun i ↦ (v i).comp ⟨e, he.continuous⟩) :=
    LinearIndependent.of_comp (continuousToL2 (μ : Measure X)).toLinearMap hve.linearIndependent
  let w : Fin n → S := fun i ↦ ⟨(v i).comp ⟨e, he.continuous⟩, hST _ (b i).property⟩
  have hclass := subspaceCoordinateClass_eq_of_orthonormal_family
    (μ : Measure X) S p n hS w hve hie
  rw [hclass]
  change Quotient.mk _ ((bestApproximationCoordinatePair (ν : Measure Y) p v hi).comap
    ⟨e, he.continuous⟩) = _
  rw [bestApproximationCoordinatePair_comap μ ν e he hμ p hp v hi hie]

end PaperN.PartII
