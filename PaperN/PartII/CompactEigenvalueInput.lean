import PaperN.PartII.CutoffIdentification

namespace PaperN.PartII
open MeasureTheory Metric Set
universe u

/-- The finite-away-from-zero consequence of Muscat 14.19/15.22 for real
compact self-adjoint operators. Only this general cited result is an input;
its inhabitant is not asserted here. -/
def CompactEigenvalueFinitenessInput : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H), IsCompactOperator T → IsSelfAdjoint T →
    ∀ η : ℝ, 0 < η → Set.Finite {a : ℝ | η < |a| ∧ Module.End.HasEigenvalue T.toLinearMap a}

variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]

theorem spectralCutoff_finiteDimensional (hs : CompactEigenvalueFinitenessInput.{u})
    (hc : IsCompactOperator (distanceOperator μ)) (ha : IsSelfAdjoint (distanceOperator μ))
    {η : ℝ} (hη : 0 < η) : FiniteDimensional ℝ (spectralCutoff μ η) :=
  spectralCutoff_finiteDimensional_of_finite μ hc hη
    (hs (Lp ℝ 2 μ) (distanceOperator μ) hc ha η hη)

/-- Positive dimension of every sufficiently small positive cutoff, conditional only
on the general cited eigenvalue finiteness input and the operator hypotheses. -/
theorem spectralCutoff_positive_finrank [Nontrivial X]
    (hs : CompactEigenvalueFinitenessInput.{u})
    (hc : IsCompactOperator (distanceOperator μ)) (ha : IsSelfAdjoint (distanceOperator μ)) :
    ∃ δ > 0, ∀ η : ℝ, 0 < η → η < δ → 0 < Module.finrank ℝ (spectralCutoff μ η) := by
  obtain ⟨δ,hδ,h⟩ := spectralCutoff_nonzero μ hc ha
  refine ⟨δ,hδ,fun η hη hηδ ↦ ?_⟩
  obtain ⟨g,hg,hgne⟩ := h η hηδ
  letI := spectralCutoff_finiteDimensional μ hs hc ha hη
  letI : Nontrivial (spectralCutoff μ η) :=
    nontrivial_of_ne (⟨g,hg⟩ : spectralCutoff μ η) 0
      (fun he ↦ hgne (congrArg Subtype.val he))
  exact Module.finrank_pos_iff.mpr inferInstance

end PaperN.PartII
