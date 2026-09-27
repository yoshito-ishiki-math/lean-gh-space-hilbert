import PaperN.PartII.SpectralCutoffEquiv
import PaperN.PartI.IsometryGroup

namespace PaperN.PartII
open MeasureTheory PaperN.PartI
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Inverse pullback is a left representation, rather than an antihomomorphism. -/
noncomputable def spectralIsometryAction (μ : ProbabilityMeasure X)
    [(μ : Measure X).IsOpenPosMeasure]
    (hinv : ∀ g : X ≃ᵢ X, μ.map g.continuous.measurable.aemeasurable = μ) (η : ℝ) :
    (X ≃ᵢ X) →* (spectralCutoff (μ : Measure X) η ≃ₗ[ℝ] spectralCutoff (μ : Measure X) η) where
  toFun g := spectralCutoffPullbackEquiv μ μ g.symm (hinv g.symm) η
  map_one' := by
    ext f x
    rfl
  map_mul' g h := by
    ext f x
    rfl

/-- The exact inverse convention of the function-space action. -/
theorem spectralIsometryAction_apply (μ : ProbabilityMeasure X)
    [(μ : Measure X).IsOpenPosMeasure]
    (hinv : ∀ g : X ≃ᵢ X, μ.map g.continuous.measurable.aemeasurable = μ) (η : ℝ)
    (g : X ≃ᵢ X) (f : spectralCutoff (μ : Measure X) η) (x : X) :
    ((spectralIsometryAction μ hinv η g f : spectralCutoff (μ : Measure X) η) : C(X, ℝ)) x =
      (f : C(X, ℝ)) (g.symm x) := rfl

/-- Every orbit map is continuous in the actual continuous-function subspace topology. -/
theorem continuous_spectralIsometryAction_orbit (μ : ProbabilityMeasure X)
    [(μ : Measure X).IsOpenPosMeasure]
    (hinv : ∀ g : X ≃ᵢ X, μ.map g.continuous.measurable.aemeasurable = μ) (η : ℝ)
    (f : spectralCutoff (μ : Measure X) η) :
    Continuous (fun g : X ≃ᵢ X ↦ spectralIsometryAction μ hinv η g f) := by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (f : C(X, ℝ)).continuous.comp
    (continuous_isometryGroup_eval.comp (continuous_inv.prodMap continuous_id))

/-- Invariance of the measure preserves the integral inner product of spectral functions. -/
theorem spectralIsometryAction_integral_mul (μ : ProbabilityMeasure X)
    [(μ : Measure X).IsOpenPosMeasure]
    (hinv : ∀ g : X ≃ᵢ X, μ.map g.continuous.measurable.aemeasurable = μ) (η : ℝ)
    (g : X ≃ᵢ X) (f h : spectralCutoff (μ : Measure X) η) :
    (∫ x, ((spectralIsometryAction μ hinv η g f : spectralCutoff (μ : Measure X) η) : C(X, ℝ)) x *
      ((spectralIsometryAction μ hinv η g h : spectralCutoff (μ : Measure X) η) : C(X, ℝ)) x
      ∂(μ : Measure X)) = ∫ x, (f : C(X, ℝ)) x * (h : C(X, ℝ)) x ∂(μ : Measure X) := by
  have he := congrArg (fun ν : ProbabilityMeasure X ↦
    ∫ x, (f : C(X, ℝ)) x * (h : C(X, ℝ)) x ∂(ν : Measure X)) (hinv g.symm)
  rw [ProbabilityMeasure.toMeasure_map] at he
  have hm : AEStronglyMeasurable (fun x ↦ (f : C(X, ℝ)) x * (h : C(X, ℝ)) x)
      (Measure.map g.symm (μ : Measure X)) :=
    ((f : C(X, ℝ)).continuous.mul (h : C(X, ℝ)).continuous).aestronglyMeasurable
  rw [integral_map g.symm.continuous.measurable.aemeasurable hm] at he
  exact he

/-- Every matrix coefficient in any finite basis is continuous in the uniform group topology. -/
theorem continuous_spectralIsometryAction_coefficient (μ : ProbabilityMeasure X)
    [(μ : Measure X).IsOpenPosMeasure]
    (hinv : ∀ g : X ≃ᵢ X, μ.map g.continuous.measurable.aemeasurable = μ) (η : ℝ)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ (spectralCutoff (μ : Measure X) η)) (i j : ι) :
    Continuous (fun g : X ≃ᵢ X ↦ b.repr (spectralIsometryAction μ hinv η g (b j)) i) := by
  letI := b.finiteDimensional_of_finite
  let c : spectralCutoff (μ : Measure X) η →ₗ[ℝ] ℝ :=
    (Finsupp.lapply i).comp b.repr.toLinearMap
  exact c.continuous_of_finiteDimensional.comp
    (continuous_spectralIsometryAction_orbit μ hinv η (b j))

/-- The action for the actual selected measure used by the local-model construction. -/
noncomputable def selectedSpectralIsometryAction
    (hm : GHPMetricInput.{0}) (hs : InvariantFiberLawSelectionStatement hm)
    (X : MeasuredCompact.{0}) (η : ℝ) :
    (X ≃ᵢ X) →* (spectralCutoff (selectedProbability hm hs X : Measure X) η ≃ₗ[ℝ]
      spectralCutoff (selectedProbability hm hs X : Measure X) η) := by
  letI : (selectedProbability hm hs X : Measure X).IsOpenPosMeasure :=
    openPos_of_support_eq_univ _ (selectedProbability_fullSupport_invariant hm hs X).1
  exact spectralIsometryAction (selectedProbability hm hs X)
    (fun g ↦ selectedProbability_natural hm hs X X g) η

end PaperN.PartII
