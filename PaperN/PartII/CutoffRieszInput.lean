import PaperN.PartII.TwoCircleProjection

namespace PaperN.PartII
universe u

/-- Cited compact Riesz range theorem, specialized to two real-diameter circles.
Anselone--Palmer (1968), p.429, spectral subspaces and Section 7, together with
compact spectral finiteness away from zero (Muscat 14.19). No inhabitant is asserted.
This input contains no metric-space kernel, restriction map, or real-function claim. -/
def CompactCutoffRieszRangeInput : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (U : E →L[ℂ] E), IsCompactOperator U →
    ∀ (η B : ℝ), 0 < η → η < B →
    (∀ z ∈ spectrum ℂ U, z.im = 0 ∧ ‖z‖ < B) →
    (η : ℂ) ∈ resolventSet ℂ U → ((-η : ℝ) : ℂ) ∈ resolventSet ℂ U →
    LinearMap.range (cutoffCircleOperator U η B).toLinearMap =
      ⨆ a : ℂ, ⨆ (_ : η < ‖a‖), Module.End.maxGenEigenspace U.toLinearMap a
end PaperN.PartII
