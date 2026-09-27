import PaperN.PartI.UniverseGHP
import PaperN.PartI.GHPRetraction

namespace PaperN.PartI
open MeasureTheory Set GromovHausdorff
universe u v

namespace MeasuredEquiv
 theorem fullSupport {X : MeasuredCompact.{u}} {Y : MeasuredCompact.{v}}
    (e : MeasuredEquiv X Y) (h : X.measure.support = univ) : Y.measure.support = univ := by
  haveI := openPos_of_support_eq_univ X.measure h
  haveI : Measure.IsOpenPosMeasure Y.measure := by
    constructor
    intro U hU hne
    rw [← e.map_measure, Measure.map_apply e.iso.continuous.measurable hU.measurableSet]
    exact (hU.preimage e.iso.continuous).measure_ne_zero _ (hne.preimage e.iso.surjective)
  exact Measure.support_eq_univ

 theorem invariantFullSupport {X : MeasuredCompact.{u}} {Y : MeasuredCompact.{v}}
    (e : MeasuredEquiv X Y) (h : X.InvariantFullSupport) : Y.InvariantFullSupport := by
  refine ⟨e.fullSupport h.1, ?_⟩
  intro g
  let k := (e.iso.trans g).trans e.iso.symm
  have hk := h.2 k
  have hh : (g : Y → Y) ∘ e.iso = e.iso ∘ k := by
    funext x
    exact (e.iso.apply_symm_apply (g (e.iso x))).symm
  rw [← e.map_measure, Measure.map_map g.continuous.measurable e.iso.continuous.measurable, hh,
    ← Measure.map_map e.iso.continuous.measurable k.continuous.measurable, hk]
end MeasuredEquiv

theorem smallMeasuredClass_forget (q : MeasuredGHSpace.{u}) :
    (smallMeasuredClass q).forget = q.forget := by
  induction q using Quotient.inductionOn with | _ X =>
    exact toGHSpace_eq_toGHSpace_iff_isometryEquiv.mpr ⟨(smallMeasuredEquiv X).iso⟩

theorem smallMeasuredClass_invariantFullSupport (q : MeasuredGHSpace.{u}) :
    (smallMeasuredClass q).invariantFullSupport ↔ q.invariantFullSupport := by
  induction q using Quotient.inductionOn with | _ X =>
    exact ⟨(smallMeasuredEquiv X).invariantFullSupport,
      (smallMeasuredEquiv X).symm.invariantFullSupport⟩

theorem smallMeasuredClass_fullSupport (q : MeasuredGHSpace.{u}) :
    (smallMeasuredClass q).fullSupport ↔ q.fullSupport := by
  induction q using Quotient.inductionOn with | _ X =>
    exact ⟨(smallMeasuredEquiv X).fullSupport, (smallMeasuredEquiv X).symm.fullSupport⟩
/-- The retract corollary in every universe, still with only the original six small inputs. -/
theorem ghpRetraction_universe (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hc : GHPCommonEmbeddingInput.{0}) (hg : GHCommonEmbeddingInput.{0})
    (ha : ProbabilityApproximationInput.{0}) (hv : InvariantValovInput hm hp hc) :
    GHPRetractionStatement (GHPMetricInput.universe.{u} hm) := by
  let hu := GHPMetricInput.universe.{u} hm
  letI := hm.metricSpace
  letI := hu.metricSpace
  let E := measuredUniverseIsometry.{u} hm
  obtain ⟨s, hs, _, hfull, _⟩ := ghpRetraction_spec hm hp hc hg ha hv
  let t : C(GHSpace, MeasuredGHSpace.{u}) := ⟨E.symm ∘ s, E.symm.continuous.comp s.continuous⟩
  let p : C(MeasuredGHSpace.{u}, GHSpace) :=
    ⟨MeasuredGHSpace.forget, (ghpForgetLipschitz_spec hu).continuous⟩
  have h : Function.LeftInverse p t := by
    intro q
    change (E.symm (s q)).forget = q
    rw [← smallMeasuredClass_forget]
    change (E (E.symm (s q))).forget = q
    rw [E.apply_symm_apply]
    exact hs q
  refine ⟨t, h, h.isEmbedding p.continuous t.continuous, ?_,
    ⟨sectionRangeHomeomorph t p h⟩, exists_range_retraction t p h,
    exists_subspace_range_retraction t p h⟩
  intro q
  have hi := smallMeasuredClass_invariantFullSupport (t q)
  have hf := smallMeasuredClass_fullSupport (t q)
  have he : smallMeasuredClass (t q) = s q := E.apply_symm_apply (s q)
  rw [he] at hi hf
  exact ⟨hi.mp (hfull q).1, hf.mp (hfull q).2⟩
/-- The universe extension of the measure gives exactly the same selected measured class. -/
theorem universalProbability_section (hm : GHPMetricInput.{0})
    (hs : InvariantFiberLawSelectionStatement hm) (X : MeasuredCompact.{u}) :
    smallMeasuredClass (X.withProbability (universalProbability hm hs X)).toMeasuredGHSpace =
      selectedGHSection hm hs (toGHSpace X) := by
  let Y := (smallCarrier X).withProbability (selectedProbability hm hs (smallCarrier X))
  let e : MeasuredEquiv Y (X.withProbability (universalProbability hm hs X)) :=
    ⟨smallCarrierEquiv X, rfl⟩
  let f := (smallMeasuredEquiv (X.withProbability (universalProbability hm hs X))).trans e.symm
  exact Quotient.sound ⟨f.iso, f.map_measure⟩
end PaperN.PartI
