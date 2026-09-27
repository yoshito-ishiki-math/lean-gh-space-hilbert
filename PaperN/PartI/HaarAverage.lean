import PaperN.PartI.IsometryGroup
import PaperN.PartI.FullSupportProbability
import PaperN.PartI.Barycenter
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.LIntegral

namespace PaperN.PartI
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

noncomputable instance isometryGroupMeasurable : MeasurableSpace (X ≃ᵢ X) := borel _
instance isometryGroupBorel : BorelSpace (X ≃ᵢ X) := ⟨rfl⟩

/-- Haar measure normalized on the whole compact group. -/
noncomputable def isometryHaar : Measure (X ≃ᵢ X) := haarMeasure ⊤

instance isometryHaar_probability : IsProbabilityMeasure (isometryHaar (X := X)) := by
  constructor
  exact haarMeasure_self (K₀ := ⊤)

instance isometryHaar_leftInvariant : IsMulLeftInvariant (isometryHaar (X := X)) := by
  unfold isometryHaar
  infer_instance

noncomputable def orbitProbability (μ : ProbabilityMeasure X) (g : X ≃ᵢ X) :
    ProbabilityMeasure X := μ.map g.continuous.measurable.aemeasurable

lemma measurable_orbitProbability (μ : ProbabilityMeasure X) : Measurable (orbitProbability μ) := by
  apply Measurable.subtype_mk
  apply Measure.measurable_of_measurable_coe
  intro S hS
  change Measurable (fun g : X ≃ᵢ X ↦ Measure.map g (μ : Measure X) S)
  simp_rw [Measure.map_apply (IsometryEquiv.continuous _).measurable hS]
  have he : Measurable (fun p : (X ≃ᵢ X) × X ↦ p.1 p.2) :=
    continuous_isometryGroup_eval.measurable
  exact measurable_measure_prodMk_left (ν := (μ : Measure X)) (he hS)

/-- Average the orbit law using the previously constructed barycenter. -/
noncomputable def haarAverage (μ : ProbabilityMeasure X) : ProbabilityMeasure X :=
  barycenter (ProbabilityMeasure.map (⟨isometryHaar, inferInstance⟩ : ProbabilityMeasure (X ≃ᵢ X))
    (measurable_orbitProbability μ).aemeasurable)

lemma haarAverage_apply (μ : ProbabilityMeasure X) {S : Set X} (hS : MeasurableSet S) :
    (haarAverage μ : Measure X) S = ∫⁻ g : X ≃ᵢ X, (μ : Measure X) (g ⁻¹' S) ∂isometryHaar := by
  rw [haarAverage, barycenter_apply _ hS]
  change (∫⁻ ν : ProbabilityMeasure X, (ν : Measure X) S
    ∂Measure.map (orbitProbability μ) isometryHaar) = _
  rw [lintegral_map (show Measurable (fun ν : ProbabilityMeasure X ↦ (ν : Measure X) S)
    from (Measure.measurable_coe hS).comp measurable_subtype_coe)
    (measurable_orbitProbability μ)]
  apply lintegral_congr
  intro g
  exact Measure.map_apply g.continuous.measurable hS

lemma haarAverage_invariant (μ : ProbabilityMeasure X) (h : X ≃ᵢ X) :
    Measure.map h (haarAverage μ : Measure X) = (haarAverage μ : Measure X) := by
  ext S hS
  rw [Measure.map_apply h.continuous.measurable hS,
    haarAverage_apply μ (h.continuous.measurable hS), haarAverage_apply μ hS]
  change (∫⁻ g : X ≃ᵢ X, (μ : Measure X) ((h * g) ⁻¹' S) ∂isometryHaar) = _
  exact lintegral_mul_left_eq_self (fun g : X ≃ᵢ X ↦ (μ : Measure X) (g ⁻¹' S)) h

lemma haarAverage_fullSupport (μ : ProbabilityMeasure X) [IsOpenPosMeasure (μ : Measure X)] :
    IsOpenPosMeasure (haarAverage μ : Measure X) := by
  constructor
  intro U hU hne
  rw [haarAverage_apply μ hU.measurableSet]
  have hm : Measurable (fun g : X ≃ᵢ X ↦ (μ : Measure X) (g ⁻¹' U)) := by
    have h := (Measure.measurable_coe hU.measurableSet).comp
      (measurable_subtype_coe.comp (measurable_orbitProbability μ))
    change Measurable (fun g : X ≃ᵢ X ↦ Measure.map g (μ : Measure X) U) at h
    simpa only [Measure.map_apply (IsometryEquiv.continuous _).measurable hU.measurableSet] using h
  intro hz
  have hae := (lintegral_eq_zero_iff hm).1 hz
  have hfalse : ∀ᵐ g : X ≃ᵢ X ∂isometryHaar, False := by
    filter_upwards [hae] with g hg
    have hne' : (g ⁻¹' U).Nonempty := hne.preimage g.surjective
    exact ((hU.preimage g.continuous).measure_ne_zero (μ : Measure X) hne') hg
  have hzHaar : isometryHaar (X := X) = 0 := by simpa using hfalse
  have := congrArg (fun m : Measure (X ≃ᵢ X) ↦ m univ) hzHaar
  simp at this

/-- lem:invariant-full-support, with no outside theorem left as a hypothesis. -/
theorem exists_invariant_fullSupport_probability [Nonempty X] :
    ∃ μ : ProbabilityMeasure X, (μ : Measure X).support = univ ∧
      ∀ g : X ≃ᵢ X, Measure.map g (μ : Measure X) = (μ : Measure X) := by
  let μ := fullSupportProbability (X := X)
  haveI : IsOpenPosMeasure (μ : Measure X) := denseAtomicMeasure_fullSupport
  haveI := haarAverage_fullSupport μ
  exact ⟨haarAverage μ, Measure.support_eq_univ, haarAverage_invariant μ⟩

end PaperN.PartI
