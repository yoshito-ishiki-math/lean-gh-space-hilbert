import PaperN.PartI.ProkhorovIsometry
import PaperN.PartI.GHPExternal

namespace PaperN.PartI
open MeasureTheory Set Filter TopologicalSpace
open scoped Topology
universe u
namespace MeasuredCompact

noncomputable def isometryDefect (X : MeasuredCompact.{u}) (g : X ≃ᵢ X) : ℝ :=
  levyProkhorovDist X.measure (Measure.map g X.measure)

def HasIsometryDefect (X : MeasuredCompact.{u}) (r : ℝ) : Prop :=
  ∃ g : X ≃ᵢ X, r ≤ X.isometryDefect g

theorem isometryDefect_conjugate {X Y : MeasuredCompact.{u}} (e : X ≃ᵢ Y)
    (he : Measure.map e X.measure = Y.measure) (g : X ≃ᵢ X) :
    Y.isometryDefect (e.symm.trans (g.trans e)) = X.isometryDefect g := by
  let k := e.symm.trans (g.trans e)
  have hk : (k : Y → Y) ∘ e = e ∘ g := by
    funext x
    simp [k]
  change levyProkhorovDist Y.measure (Measure.map k Y.measure) = _
  rw [← he, Measure.map_map k.continuous.measurable e.continuous.measurable, hk,
    ← Measure.map_map e.continuous.measurable g.continuous.measurable,
    levyProkhorovDist_map_isometry e e.isometry]
  rfl

theorem hasIsometryDefect_of_isomorphic {X Y : MeasuredCompact.{u}}
    (h : X.Isomorphic Y) {r : ℝ} (hr : X.HasIsometryDefect r) : Y.HasIsometryDefect r := by
  obtain ⟨e, he⟩ := h
  obtain ⟨g, hg⟩ := hr
  exact ⟨e.symm.trans (g.trans e), (isometryDefect_conjugate e he g) ▸ hg⟩

theorem hasIsometryDefect_iff {X Y : MeasuredCompact.{u}} (h : X.Isomorphic Y) (r : ℝ) :
    X.HasIsometryDefect r ↔ Y.HasIsometryDefect r :=
  ⟨hasIsometryDefect_of_isomorphic h, hasIsometryDefect_of_isomorphic (isomorphic_symm h)⟩

theorem isometryDefect_eq_zero_iff (X : MeasuredCompact.{u}) (g : X ≃ᵢ X) :
    X.isometryDefect g = 0 ↔ Measure.map g X.measure = X.measure := by
  let ν := X.probability.map g.continuous.measurable.aemeasurable
  change dist (LevyProkhorov.ofMeasure X.probability) (LevyProkhorov.ofMeasure ν) = 0 ↔ _
  rw [dist_eq_zero]
  constructor
  · intro h
    have hp : X.probability = ν := congrArg LevyProkhorov.toMeasure h
    exact (congrArg ProbabilityMeasure.toMeasure hp).symm
  · intro h
    have hp : ν = X.probability := ProbabilityMeasure.toMeasure_injective h
    exact congrArg LevyProkhorov.ofMeasure hp.symm

/-- Invariance under all isometries is equivalent to excluding every positive dyadic defect. -/
theorem invariant_iff_no_dyadic_defect (X : MeasuredCompact.{u}) :
    (∀ g : X ≃ᵢ X, Measure.map g X.measure = X.measure) ↔
      ∀ n : ℕ, ¬ X.HasIsometryDefect ((1 / 2 : ℝ) ^ n) := by
  constructor
  · intro h n ⟨g, hg⟩
    rw [(isometryDefect_eq_zero_iff X g).mpr (h g)] at hg
    exact (not_le_of_gt (by positivity)) hg
  · intro h g
    apply (isometryDefect_eq_zero_iff X g).mp
    have hn : 0 ≤ X.isometryDefect g := ENNReal.toReal_nonneg
    by_contra hne
    obtain ⟨n, hn'⟩ := exists_pow_lt_of_lt_one (lt_of_le_of_ne hn (Ne.symm hne))
      (show (1 / 2 : ℝ) < 1 by norm_num)
    exact h n ⟨g, hn'.le⟩
end MeasuredCompact

namespace MeasuredGHSpace
/-- Defect predicates are invariant under changing the entire measured carrier. -/
def hasIsometryDefect (r : ℝ) (q : MeasuredGHSpace.{u}) : Prop :=
  Quotient.liftOn q (fun X ↦ X.HasIsometryDefect r)
    (fun _ _ h ↦ propext (MeasuredCompact.hasIsometryDefect_iff h r))

/-- All self-isometries preserve the measure, without imposing full support. -/
def invariant (q : MeasuredGHSpace.{u}) : Prop :=
  Quotient.liftOn q (fun X ↦ ∀ g : X ≃ᵢ X, Measure.map g X.measure = X.measure) (by
    intro X Y h
    apply propext
    rw [MeasuredCompact.invariant_iff_no_dyadic_defect, MeasuredCompact.invariant_iff_no_dyadic_defect]
    exact forall_congr' fun n ↦ not_congr (MeasuredCompact.hasIsometryDefect_iff h _))
end MeasuredGHSpace
end PaperN.PartI
