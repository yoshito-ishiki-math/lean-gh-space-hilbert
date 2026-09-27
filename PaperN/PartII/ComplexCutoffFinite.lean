import PaperN.PartII.TwoCircleProjection
import PaperN.PartII.CompactEigenvalueInput

namespace PaperN.PartII
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem complex_cutoff_eigenvalues_finite (hf : CompactEigenvalueFinitenessInput.{u})
    (U : H →L[ℂ] H) (hc : IsCompactOperator U) (hs : U.toLinearMap.IsSymmetric)
    (η : ℝ) (hη : 0 < η) :
    Set.Finite {a : ℂ | η < ‖a‖ ∧ Module.End.HasEigenvalue U.toLinearMap a} := by
  letI realInner : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  letI scalarTower : IsScalarTower ℝ ℂ H := IsScalarTower.restrictScalars ℝ ℂ H
  have hsym : (U.restrictScalars ℝ).toLinearMap.IsSymmetric := hs.restrictScalars
  have hfin := hf H (U.restrictScalars ℝ) hc hsym.isSelfAdjoint η hη
  apply (hfin.image (fun a : ℝ ↦ (a : ℂ))).subset
  intro a ha
  have hre : a.im = 0 := by
    have hh := hs.conj_eigenvalue_eq_self ha.2
    have hi := congrArg Complex.im hh
    simp only [Complex.conj_im] at hi
    linarith
  have he : a = (a.re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using hre
  refine ⟨a.re, ⟨?_, ?_⟩, he.symm⟩
  · have hh : ‖a‖ = |a.re| := by
      calc ‖a‖ = ‖(a.re : ℂ)‖ := congrArg norm he
           _ = |a.re| := by simp
    simpa only [hh] using ha.1
  · obtain ⟨v, hv, hn⟩ := ha.2.exists_hasEigenvector
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨?_, hn⟩
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    change U v = a.re • v
    change U v = a • v at hv
    rw [he] at hv
    simpa using hv

abbrev complexAlgebraicCutoff (U : H →L[ℂ] H) (η : ℝ) : Submodule ℂ H :=
  ⨆ a : ℂ, ⨆ (_ : η < ‖a‖), Module.End.eigenspace U.toLinearMap a

theorem complexAlgebraicCutoff_finiteDimensional (hf : CompactEigenvalueFinitenessInput.{u})
    (U : H →L[ℂ] H) (hc : IsCompactOperator U) (hs : U.toLinearMap.IsSymmetric)
    (η : ℝ) (hη : 0 < η) : FiniteDimensional ℂ (complexAlgebraicCutoff U η) := by
  classical
  let A := {a : ℂ | η < ‖a‖ ∧ Module.End.HasEigenvalue U.toLinearMap a}
  letI finiteA : Finite A := (complex_cutoff_eigenvalues_finite hf U hc hs η hη).to_subtype
  let V (a : A) := Module.End.eigenspace U.toLinearMap a.val
  have heq : complexAlgebraicCutoff U η = ⨆ a : A, V a := by
    apply le_antisymm
    · apply iSup_le
      intro a
      apply iSup_le
      intro ha
      by_cases he : Module.End.HasEigenvalue U.toLinearMap a
      · exact le_iSup V ⟨a, ha, he⟩
      · have hz : Module.End.eigenspace U.toLinearMap a = ⊥ := not_ne_iff.mp he
        rw [hz]
        exact bot_le
    · apply iSup_le
      intro a
      exact le_iSup_of_le a.val (le_iSup_of_le a.property.1 le_rfl)
  letI finiteV (a : A) : FiniteDimensional ℂ (V a) :=
    ContinuousLinearMap.finite_dimensional_eigenspace hc a.val
      (norm_pos_iff.mp (hη.trans a.property.1))
  rw [heq]
  infer_instance

theorem closedEigenSpan_cutoff_eq_algebraic (hf : CompactEigenvalueFinitenessInput.{u})
    (U : H →L[ℂ] H) (hc : IsCompactOperator U) (hs : U.toLinearMap.IsSymmetric)
    (η : ℝ) (hη : 0 < η) :
    closedEigenSpan U {a | η < ‖a‖} = complexAlgebraicCutoff U η := by
  letI finiteCutoff := complexAlgebraicCutoff_finiteDimensional hf U hc hs η hη
  exact (Submodule.closed_of_finiteDimensional (complexAlgebraicCutoff U η)).submodule_topologicalClosure_eq

theorem cutoffCircle_range_eq_algebraic (hf : CompactEigenvalueFinitenessInput.{u})
    (U : H →L[ℂ] H) (hc : IsCompactOperator U) (hs : U.toLinearMap.IsSymmetric)
    (η B : ℝ) (hη : 0 < η) (hB : η < B)
    (hbound : ∀ z ∈ spectrum ℂ U, z.im = 0 ∧ ‖z‖ < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ U) (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ U) :
    LinearMap.range (cutoffCircleOperator U η B).toLinearMap = complexAlgebraicCutoff U η := by
  rw [cutoffCircle_eq_starProjection U hc hs η B hη hB hbound hp hn,
    Submodule.range_starProjection]
  exact closedEigenSpan_cutoff_eq_algebraic hf U hc hs η hη

theorem cutoffCircle_range_finiteDimensional (hf : CompactEigenvalueFinitenessInput.{u})
    (U : H →L[ℂ] H) (hc : IsCompactOperator U) (hs : U.toLinearMap.IsSymmetric)
    (η B : ℝ) (hη : 0 < η) (hB : η < B)
    (hbound : ∀ z ∈ spectrum ℂ U, z.im = 0 ∧ ‖z‖ < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ U) (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ U) :
    FiniteDimensional ℂ (LinearMap.range (cutoffCircleOperator U η B).toLinearMap) := by
  rw [cutoffCircle_range_eq_algebraic hf U hc hs η B hη hB hbound hp hn]
  exact complexAlgebraicCutoff_finiteDimensional hf U hc hs η hη

namespace ComplexKernel
open MeasureTheory
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]

theorem distance_cutoffCircle_range_eq_algebraic (hf : CompactEigenvalueFinitenessInput.{u})
    (η : ℝ) (hη : 0 < η)
    (hp : (η : ℂ) ∈ resolventSet ℂ (distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (distanceOperator μ)) :
    LinearMap.range (cutoffCircleOperator (distanceOperator μ) η
      (Metric.diam (Set.univ : Set X) + η + 1)).toLinearMap =
      complexAlgebraicCutoff (distanceOperator μ) η := by
  rw [distance_cutoffCircle_explicit μ η hη hp hn, Submodule.range_starProjection]
  exact closedEigenSpan_cutoff_eq_algebraic hf _
    (AmbientKernel.distanceOperator_compact (ContinuousMap.id X) μ isometry_id)
    (distanceOperator_symmetric μ) η hη

theorem distance_complexAlgebraicCutoff_finiteDimensional
    (hf : CompactEigenvalueFinitenessInput.{u}) (η : ℝ) (hη : 0 < η) :
    FiniteDimensional ℂ (complexAlgebraicCutoff (distanceOperator μ) η) :=
  complexAlgebraicCutoff_finiteDimensional hf _
    (AmbientKernel.distanceOperator_compact (ContinuousMap.id X) μ isometry_id)
    (distanceOperator_symmetric μ) η hη
end ComplexKernel
end PaperN.PartII
