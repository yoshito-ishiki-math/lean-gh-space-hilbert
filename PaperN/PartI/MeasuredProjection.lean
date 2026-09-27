import PaperN.PartI.GHPDistance
import PaperN.PartI.Solution
import Mathlib.Topology.MetricSpace.GromovHausdorff

namespace PaperN.PartI
open MeasureTheory Set Metric GromovHausdorff
open scoped ENNReal
universe u

namespace MeasuredGHSpace
/-- Forget the measure, retaining the entire compact carrier. -/
noncomputable def forget (x : MeasuredGHSpace.{u}) : GHSpace :=
  Quotient.liftOn x (fun X ↦ toGHSpace X) (by
    intro X Y h
    exact toGHSpace_eq_toGHSpace_iff_isometryEquiv.2 ⟨h.choose⟩)

lemma forget_mk (X : MeasuredCompact.{u}) : forget (Quotient.mk _ X) = toGHSpace X := rfl
end MeasuredGHSpace

/-- The Hausdorff term controls the entire carrier, including points outside measure support. -/
lemma ghDist_le_ghpDist (X Y : MeasuredCompact.{u}) : ghDist X Y ≤ ghpDist X Y := by
  apply (ENNReal.ofReal_le_iff_le_toReal (ghpEDist_ne_top X Y)).1
  apply le_iInf
  intro C
  apply (ENNReal.ofReal_le_iff_le_toReal C.cost_ne_top).2
  exact (ghDist_le_hausdorffDist C.left_isometry C.right_isometry).trans
    (ENNReal.toReal_mono C.cost_ne_top (le_max_left _ _))

namespace MeasuredGHSpace
lemma forget_distance_le (x y : MeasuredGHSpace.{u}) :
    dist (forget x) (forget y) ≤ distance x y := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact ghDist_le_ghpDist X Y
end MeasuredGHSpace

namespace MeasuredCompact
/-- Invariant full support is preserved by whole-carrier measured isomorphisms. -/
lemma invariantFullSupport_of_isomorphic {X Y : MeasuredCompact.{u}}
    (h : X.Isomorphic Y) (hX : X.InvariantFullSupport) : Y.InvariantFullSupport := by
  obtain ⟨e, he⟩ := h
  haveI : Measure.IsOpenPosMeasure X.measure := openPos_of_support_eq_univ _ hX.1
  haveI : Measure.IsOpenPosMeasure Y.measure := by
    constructor
    intro U hU hne
    rw [← he, Measure.map_apply e.continuous.measurable hU.measurableSet]
    exact (hU.preimage e.continuous).measure_ne_zero X.measure (hne.preimage e.surjective)
  refine ⟨Measure.support_eq_univ, ?_⟩
  intro g
  let k : X ≃ᵢ X := (e.trans g).trans e.symm
  have hk := hX.2 k
  have hh : (g : Y → Y) ∘ e = e ∘ k := by
    funext x
    exact (e.apply_symm_apply (g (e x))).symm
  rw [← he, Measure.map_map g.continuous.measurable e.continuous.measurable, hh,
    ← Measure.map_map e.continuous.measurable k.continuous.measurable, hk]

lemma invariantFullSupport_iff {X Y : MeasuredCompact.{u}} (h : X.Isomorphic Y) :
    X.InvariantFullSupport ↔ Y.InvariantFullSupport :=
  ⟨invariantFullSupport_of_isomorphic h,
    invariantFullSupport_of_isomorphic (isomorphic_symm h)⟩
end MeasuredCompact

namespace MeasuredGHSpace
/-- The invariant full-support property descends to the measured-isometry quotient. -/
def invariantFullSupport (x : MeasuredGHSpace.{u}) : Prop :=
  Quotient.liftOn x MeasuredCompact.InvariantFullSupport
    (fun _ _ h ↦ propext (MeasuredCompact.invariantFullSupport_iff h))
end MeasuredGHSpace

/-- The manuscript's invariant full-support subspace, before any topology is asserted. -/
def InvariantMeasuredGHSpace := {x : MeasuredGHSpace.{u} // x.invariantFullSupport}

/-- Every small compact carrier admits a representative in the invariant subspace. -/
theorem invariant_projection_surjective :
    Function.Surjective (fun x : InvariantMeasuredGHSpace.{0} ↦ x.val.forget) := by
  intro q
  letI : MeasurableSpace q.Rep := borel q.Rep
  letI : BorelSpace q.Rep := ⟨rfl⟩
  obtain ⟨μ, hμ, hInv⟩ := exists_invariant_fullSupport_probability (X := q.Rep)
  let M : MeasuredCompact := ⟨q.Rep, inferInstance, inferInstance, inferInstance, μ⟩
  refine ⟨⟨Quotient.mk _ M, ?_⟩, ?_⟩
  · exact ⟨hμ, hInv⟩
  · exact q.toGHSpace_rep
theorem ghProjectionBound_spec : GHProjectionBoundStatement.{u} := ghDist_le_ghpDist

theorem invariantProjectionSurjectivity_spec : InvariantProjectionSurjectivityStatement := by
  intro q
  obtain ⟨x, hx⟩ := invariant_projection_surjective q
  obtain ⟨M, hM⟩ := Quotient.exists_rep x.val
  refine ⟨M, ?_, ?_⟩
  · have h := x.property
    rw [← hM] at h
    exact h
  · exact (congrArg MeasuredGHSpace.forget hM).trans hx
end PaperN.PartI
