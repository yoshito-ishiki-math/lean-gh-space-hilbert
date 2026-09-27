import PaperN.PartII.LocalModelExistence

namespace PaperN.PartII
open PaperN.PartI GromovHausdorff Set

namespace LocalModel
variable {X₀ : MeasuredCompact.{0}} {τ : ℝ}

/-- Restriction preserves every local-model condition and the same coordinate data. -/
noncomputable def restrict (M : LocalModel X₀ τ) (U : Set GHSpace)
    (hU : IsOpen U) (hcenter : toGHSpace X₀ ∈ U) (hsub : U ⊆ M.domain) :
    LocalModel X₀ τ where
  domain := U
  domain_open := hU
  center_mem := hcenter
  dimension := M.dimension
  dimension_pos := M.dimension_pos
  coordinateClass := fun X hX ↦ M.coordinateClass X (hsub hX)
  error := M.error
  error_nonneg := fun q hq ↦ M.error_nonneg q (hsub hq)
  error_continuous := M.error_continuous.mono hsub
  center_error := M.center_error
  equivariance := fun X Y hX hY ↦ M.equivariance X Y (hsub hX) (hsub hY)
  bound := fun X hX ↦ M.bound X (hsub hX)
  representatives_converge := fun Xs X hXs hX ↦
    M.representatives_converge Xs X (fun k ↦ hsub (hXs k)) (hsub hX)
  error_eq := fun X hX ↦ M.error_eq X (hsub hX)

/-- Shrink to the strict error sublevel set around the center. -/
noncomputable def shrink (M : LocalModel X₀ τ) : LocalModel X₀ τ :=
  M.restrict (M.domain ∩ M.error ⁻¹' Iio τ)
    (M.error_continuous.isOpen_inter_preimage M.domain_open isOpen_Iio)
    ⟨M.center_mem, M.center_error⟩ inter_subset_left

/-- The shrunken neighborhood has the prescribed strict error everywhere. -/
theorem shrink_error_lt (M : LocalModel X₀ τ) (q : GHSpace)
    (hq : q ∈ M.shrink.domain) : M.shrink.error q < τ := hq.2

/-- The strict approximation bound holds for every pair in every assigned class. -/
theorem shrink_representative_error_lt (M : LocalModel X₀ τ)
    (X : MeasuredCompact.{0}) (hX : toGHSpace X ∈ M.shrink.domain)
    (a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin M.shrink.dimension)))
    (ha : Quotient.mk _ a = M.shrink.coordinateClass X hX) :
    (⨆ z : X × X, |a.pseudometric z.1 z.2 - dist z.1 z.2|) < τ := by
  rw [← M.shrink.error_eq X hX a ha]
  exact M.shrink_error_lt (toGHSpace X) hX

end LocalModel

namespace AmbientKernel
/-- Local-model existence with strict approximation throughout its open domain. -/
theorem exists_uniformly_approximating_localModel
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm) (hg : GHCommonEmbeddingInput.{0})
    (hk : DistanceKernelSpectralInput.{0})

    (hf : CompactEigenvalueFinitenessInput.{0})

    (X : MeasuredCompact.{0}) (τ : ℝ) (hτ : 0 < τ) :
    ∃ M : LocalModel X τ, ∀ q ∈ M.domain, M.error q < τ := by
  obtain ⟨M⟩ := exists_localModel hm hp hs hg hk   hf   X τ hτ
  exact ⟨M.shrink, M.shrink_error_lt⟩

end AmbientKernel
end PaperN.PartII
