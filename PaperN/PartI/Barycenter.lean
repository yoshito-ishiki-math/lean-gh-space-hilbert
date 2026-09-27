import PaperN.PartI.Definitions
import PaperN.PartI.ProbabilityTopology
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

/-! Concrete probability averaging. The construction and proof of lem:continuous-barycenter.
This uses the existing Giry measurable structure, and does not assume a barycenter axiom. -/
namespace PaperN.PartI
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal ProbabilityTheory BoundedContinuousFunction

variable {X : Type*} [MeasurableSpace X]

lemma barycenter_apply (η : ProbabilityMeasure (ProbabilityMeasure X))
    {s : Set X} (hs : MeasurableSet s) :
    (barycenter η : Measure X) s = ∫⁻ μ : ProbabilityMeasure X, (μ : Measure X) s ∂η := by
  exact Measure.bind_apply hs measurable_subtype_coe.aemeasurable

/-- Averaging commutes with integration of any nonnegative measurable test function. -/
theorem lintegral_barycenter (η : ProbabilityMeasure (ProbabilityMeasure X))
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(barycenter η : Measure X) = ∫⁻ μ : ProbabilityMeasure X, ∫⁻ x, f x ∂(μ : Measure X) ∂η := by
  exact Measure.lintegral_bind measurable_subtype_coe.aemeasurable hf.aemeasurable

/-- The averaged probability is uniquely determined by its evaluations on measurable sets. -/
theorem barycenter_unique (η : ProbabilityMeasure (ProbabilityMeasure X))
    (ν : ProbabilityMeasure X)
    (hν : ∀ s, MeasurableSet s → (ν : Measure X) s = ∫⁻ μ : ProbabilityMeasure X, (μ : Measure X) s ∂η) :
    ν = barycenter η := by
  apply ProbabilityMeasure.toMeasure_injective
  ext s hs
  exact (hν s hs).trans (barycenter_apply η hs).symm

/-- Full support is preserved under a law concentrated on full-support probabilities. -/
theorem barycenter_fullSupport [TopologicalSpace X] [OpensMeasurableSpace X]
    (η : ProbabilityMeasure (ProbabilityMeasure X))
    (hη : ∀ᵐ μ : ProbabilityMeasure X ∂(η : Measure (ProbabilityMeasure X)),
      IsOpenPosMeasure (μ : Measure X)) :
    IsOpenPosMeasure (barycenter η : Measure X) := by
  constructor
  intro U hU hne
  rw [barycenter_apply η hU.measurableSet]
  intro hzero
  have hm : Measurable (fun μ : ProbabilityMeasure X ↦ (μ : Measure X) U) :=
    (Measure.measurable_coe hU.measurableSet).comp measurable_subtype_coe
  have hz := (lintegral_eq_zero_iff hm).1 hzero
  have hfalse : ∀ᵐ μ : ProbabilityMeasure X ∂(η : Measure (ProbabilityMeasure X)), False := by
    filter_upwards [hη, hz] with μ hμ hzμ
    letI := hμ
    exact (hU.measure_ne_zero (μ : Measure X) hne) hzμ
  have hzη : (η : Measure (ProbabilityMeasure X)) = 0 := by simpa using hfalse
  have := congrArg (fun m : Measure (ProbabilityMeasure X) ↦ m univ) hzη
  simp at this

/-- Almost-sure invariance under any measurable map passes to the barycenter. -/
theorem barycenter_invariant (η : ProbabilityMeasure (ProbabilityMeasure X))
    {g : X → X} (hg : Measurable g)
    (hη : ∀ᵐ μ : ProbabilityMeasure X ∂(η : Measure (ProbabilityMeasure X)),
      Measure.map g (μ : Measure X) = (μ : Measure X)) :
    Measure.map g (barycenter η : Measure X) = (barycenter η : Measure X) := by
  ext s hs
  rw [Measure.map_apply hg hs, barycenter_apply η (hg hs), barycenter_apply η hs]
  apply lintegral_congr_ae
  filter_upwards [hη] with μ hμ
  have h := congrArg (fun m : Measure X ↦ m s) hμ
  simpa only [Measure.map_apply hg hs] using h

/-- The fixed probabilities form a weakly closed, hence Giry measurable, set. -/
theorem isClosed_invariantProbabilities [MetricSpace X] [CompactSpace X] [BorelSpace X]
    {g : X → X} (hg : Continuous g) :
    IsClosed {μ : ProbabilityMeasure X | Measure.map g (μ : Measure X) = (μ : Measure X)} := by
  have h := isClosed_eq (ProbabilityMeasure.continuous_map hg) continuous_id
  convert h using 1
  ext μ
  change Measure.map g (μ : Measure X) = (μ : Measure X) ↔
    μ.map hg.measurable.aemeasurable = μ
  exact ⟨fun hμ ↦ ProbabilityMeasure.toMeasure_injective hμ,
    fun hμ ↦ congrArg ProbabilityMeasure.toMeasure hμ⟩

/-- The mass-one formulation of invariance used in the current manuscript. -/
theorem barycenter_invariant_of_mass_one [MetricSpace X] [CompactSpace X] [BorelSpace X]
    (η : ProbabilityMeasure (ProbabilityMeasure X)) {g : X → X} (hg : Continuous g)
    (hη : (η : Measure (ProbabilityMeasure X))
      {μ | Measure.map g (μ : Measure X) = (μ : Measure X)} = 1) :
    Measure.map g (barycenter η : Measure X) = (barycenter η : Measure X) := by
  apply barycenter_invariant η hg.measurable
  exact (mem_ae_iff_prob_eq_one (isClosed_invariantProbabilities hg).measurableSet).mpr hη

/-- Average of a Dirac law, including the measure-level monad normalization. -/
theorem barycenter_dirac (μ : ProbabilityMeasure X) :
    barycenter ⟨Measure.dirac μ, inferInstance⟩ = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  exact Measure.dirac_bind measurable_subtype_coe μ

/-- Bochner integral identity, obtained from the concrete probability kernel. -/
theorem integral_barycenter (η : ProbabilityMeasure (ProbabilityMeasure X))
    {f : X → ℝ} (hf : Integrable f (barycenter η : Measure X)) :
    ∫ x, f x ∂(barycenter η : Measure X) =
      ∫ μ : ProbabilityMeasure X, ∫ x, f x ∂(μ : Measure X) ∂η := by
  let K : ProbabilityTheory.Kernel (ProbabilityMeasure X) X :=
    ⟨fun μ ↦ (μ : Measure X), measurable_subtype_coe⟩
  let L := ProbabilityTheory.Kernel.const Unit (η : Measure (ProbabilityMeasure X))
  have heq : (K ∘ₖ L) () = (barycenter η : Measure X) := rfl
  have h := ProbabilityTheory.Kernel.integral_comp (κ := L) (η := K) (a := ())
    (f := f) (heq.symm ▸ hf)
  exact h

/-- On compact metric spaces this is exactly the real continuous-test-function identity
in eq:continuous-barycenter. -/
theorem integral_barycenter_continuous [MetricSpace X] [CompactSpace X] [BorelSpace X]
    (η : ProbabilityMeasure (ProbabilityMeasure X)) (f : C(X, ℝ)) :
    ∫ x, f x ∂(barycenter η : Measure X) =
      ∫ μ : ProbabilityMeasure X, ∫ x, f x ∂(μ : Measure X) ∂η := by
  apply integral_barycenter
  exact f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Uniqueness with precisely the continuous test functions used in the manuscript. -/
theorem barycenter_unique_continuous [MetricSpace X] [CompactSpace X] [BorelSpace X]
    (η : ProbabilityMeasure (ProbabilityMeasure X)) (ν : ProbabilityMeasure X)
    (hν : ∀ f : C(X, ℝ), ∫ x, f x ∂(ν : Measure X) =
      ∫ μ : ProbabilityMeasure X, ∫ x, f x ∂(μ : Measure X) ∂η) :
    ν = barycenter η := by
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact (hν f.toContinuousMap).trans (integral_barycenter_continuous η f.toContinuousMap).symm

/-- Weak continuity of averaging laws on a fixed compact metric space. -/
theorem continuous_barycenter [MetricSpace X] [CompactSpace X] [BorelSpace X] :
    Continuous (barycenter : ProbabilityMeasure (ProbabilityMeasure X) → ProbabilityMeasure X) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.2
  intro f
  let F : ProbabilityMeasure X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun μ ↦ ∫ x, f x ∂(μ : Measure X))
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f)
    ‖f‖ (fun μ ↦ f.norm_integral_le_norm (μ : Measure X))
  have hF := ProbabilityMeasure.continuous_integral_boundedContinuousFunction F
  convert hF using 1
  ext η
  exact integral_barycenter η (f.integrable _)

end PaperN.PartI
