import PaperN.PartII.CutoffCircleRangeFactorization
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

namespace PaperN.PartII

/-- A closed subspace fixed pointwise by a compact operator is finite dimensional. -/
theorem finiteDimensional_of_compact_fixes_subspace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P : E →L[ℂ] E) (hP : IsCompactOperator P)
    (S : Submodule ℂ E) (hS : IsClosed (S : Set E))
    (hfix : ∀ x : S, P x = x) : FiniteDimensional ℂ S := by
  have hm : ∀ x : S, (P ∘ S.subtypeL) x ∈ S := by
    intro x
    change P x ∈ S
    rw [hfix]
    exact x.property
  have hc := (hP.comp_clm S.subtypeL).codRestrict hm hS
  have he : Set.codRestrict (P ∘ S.subtypeL) S hm = (id : S → S) := by
    funext x
    apply Subtype.ext
    exact hfix x
  rw [he] at hc
  exact FiniteDimensional.of_isCompactOperator_id hc

/-- The closed cutoff eigenspan of a compact self-adjoint operator is finite dimensional. -/
theorem closedEigenSpan_cutoff_finiteDimensional
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : H →L[ℂ] H) (hc : IsCompactOperator U) (hs : U.toLinearMap.IsSymmetric)
    (η B : ℝ) (hη : 0 < η) (hB : η < B)
    (hb : ∀ z ∈ spectrum ℂ U, z.im = 0 ∧ ‖z‖ < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ U) (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ U) :
    FiniteDimensional ℂ (closedEigenSpan U {a | η < ‖a‖}) := by
  have he := cutoffCircle_eq_starProjection U hc hs η B hη hB hb hp hn
  have hcompact := cutoffCircle_isCompactOperator U hc η B hη hB hb hp hn
  rw [he] at hcompact
  apply finiteDimensional_of_compact_fixes_subspace _ hcompact _
    (Submodule.isClosed_topologicalClosure _)
  exact fun x ↦ Submodule.starProjection_mem_subspace_eq_self x

/-- For compact self-adjoint operators the cutoff range is the algebraic eigenspace sum. -/
theorem cutoffCircle_range_eq_eigenspaces
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : H →L[ℂ] H) (hc : IsCompactOperator U) (hs : U.toLinearMap.IsSymmetric)
    (η B : ℝ) (hη : 0 < η) (hB : η < B)
    (hb : ∀ z ∈ spectrum ℂ U, z.im = 0 ∧ ‖z‖ < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ U) (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ U) :
    LinearMap.range (cutoffCircleOperator U η B).toLinearMap =
      ⨆ a : ℂ, ⨆ (_ : η < ‖a‖), Module.End.eigenspace U.toLinearMap a := by
  let S := ⨆ a : ℂ, ⨆ (_ : η < ‖a‖), Module.End.eigenspace U.toLinearMap a
  letI : FiniteDimensional ℂ S.topologicalClosure :=
    closedEigenSpan_cutoff_finiteDimensional U hc hs η B hη hB hb hp hn
  letI : FiniteDimensional ℂ S := FiniteDimensional.of_injective
    (Submodule.inclusion S.le_topologicalClosure) (Submodule.inclusion_injective _)
  have hclosed := (Submodule.closed_of_finiteDimensional S).submodule_topologicalClosure_eq
  rw [cutoffCircle_eq_starProjection U hc hs η B hη hB hb hp hn]
  change (closedEigenSpan U {a | η < ‖a‖}).starProjection.range = S
  rw [Submodule.range_starProjection]
  exact hclosed
end PaperN.PartII

