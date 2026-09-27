import PaperN.PartI.GHPStatements
import Mathlib.Topology.MetricSpace.Gluing

/-! Finiteness, symmetry, representative invariance, and the real max-infimum formula.
Triangle inequality, metric separation, completeness, and separability remain future work. -/
namespace PaperN.PartI
open MeasureTheory Set Metric
open scoped ENNReal
universe u
namespace CompactCoupling
variable {X Y : MeasuredCompact.{u}}
lemma cost_ne_top (C : CompactCoupling X Y) : C.cost ≠ ⊤ := by
  apply ne_of_lt
  apply max_lt
  · exact lt_top_iff_ne_top.2 (hausdorffEDist_ne_top_of_nonempty_of_bounded
      (range_nonempty _) (range_nonempty _) (isCompact_range C.left_isometry.continuous).isBounded
      (isCompact_range C.right_isometry.continuous).isBounded)
  · exact levyProkhorovEDist_lt_top _ _

def swap (C : CompactCoupling X Y) : CompactCoupling Y X where
  Carrier := C
  metric := inferInstance
  compact := inferInstance
  left := C.right
  right := C.left
  left_isometry := C.right_isometry
  right_isometry := C.left_isometry

lemma cost_swap (C : CompactCoupling X Y) : C.swap.cost = C.cost := by
  exact congrArg₂ max hausdorffEDist_comm (levyProkhorovEDist_comm _ _)

def refl (X : MeasuredCompact.{u}) : CompactCoupling X X where
  Carrier := X
  metric := inferInstance
  compact := inferInstance
  left := id
  right := id
  left_isometry := isometry_id
  right_isometry := isometry_id

lemma cost_refl (X : MeasuredCompact.{u}) : (refl X).cost = 0 := by
  simp [cost, refl, leftMeasure, rightMeasure, hausdorffEDist_self, levyProkhorovEDist_self]

/-- A witness that the infimum is over a nonempty family, even for unrelated spaces. -/
noncomputable def sum (X Y : MeasuredCompact.{u}) : CompactCoupling X Y := by
  letI := metricSpaceSum (X := X) (Y := Y)
  exact ⟨X ⊕ Y, inferInstance, inferInstance, Sum.inl, Sum.inr, isometry_inl, isometry_inr⟩
/-- Change the left representative by a whole-carrier isometry. -/
def reparamLeft {A : MeasuredCompact.{u}} (C : CompactCoupling X Y) (e : A ≃ᵢ X) :
    CompactCoupling A Y where
  Carrier := C
  metric := inferInstance
  compact := inferInstance
  left := C.left ∘ e
  right := C.right
  left_isometry := C.left_isometry.comp e.isometry
  right_isometry := C.right_isometry

lemma cost_reparamLeft {A : MeasuredCompact.{u}} (C : CompactCoupling X Y) (e : A ≃ᵢ X)
    (he : Measure.map e A.measure = X.measure) : (C.reparamLeft e).cost = C.cost := by
  change max (hausdorffEDist (range (C.left ∘ e)) (range C.right))
    (levyProkhorovEDist (Measure.map (C.left ∘ e) A.measure) C.rightMeasure) = _
  rw [e.surjective.range_comp, ← Measure.map_map C.left_isometry.continuous.measurable
    e.continuous.measurable, he]
  rfl
end CompactCoupling

lemma ghpEDist_le_cost {X Y : MeasuredCompact.{u}} (C : CompactCoupling X Y) :
    ghpEDist X Y ≤ C.cost := iInf_le _ C

lemma ghpEDist_ne_top (X Y : MeasuredCompact.{u}) : ghpEDist X Y ≠ ⊤ :=
  ne_top_of_le_ne_top (CompactCoupling.sum X Y).cost_ne_top (ghpEDist_le_cost _)

lemma ghpEDist_self (X : MeasuredCompact.{u}) : ghpEDist X X = 0 := by
  apply le_antisymm _ zero_le
  exact (ghpEDist_le_cost (CompactCoupling.refl X)).trans_eq (CompactCoupling.cost_refl X)

lemma ghpEDist_comm (X Y : MeasuredCompact.{u}) : ghpEDist X Y = ghpEDist Y X := by
  have h : ∀ A B : MeasuredCompact.{u}, ghpEDist A B ≤ ghpEDist B A := by
    intro A B
    apply le_iInf
    intro C
    exact (ghpEDist_le_cost C.swap).trans_eq C.cost_swap
  exact le_antisymm (h X Y) (h Y X)

lemma ghpEDist_congr_left {X X' : MeasuredCompact.{u}} (h : X.Isomorphic X')
    (Y : MeasuredCompact.{u}) : ghpEDist X Y = ghpEDist X' Y := by
  have hle : ∀ {A B : MeasuredCompact.{u}}, A.Isomorphic B → ghpEDist A Y ≤ ghpEDist B Y := by
    intro A B hAB
    obtain ⟨e, he⟩ := hAB
    apply le_iInf
    intro C
    exact (ghpEDist_le_cost (C.reparamLeft e)).trans_eq (C.cost_reparamLeft e he)
  exact le_antisymm (hle h) (hle (MeasuredCompact.isomorphic_symm h))

lemma ghpEDist_congr {X X' Y Y' : MeasuredCompact.{u}}
    (hX : X.Isomorphic X') (hY : Y.Isomorphic Y') : ghpEDist X Y = ghpEDist X' Y' := by
  rw [ghpEDist_congr_left hX, ghpEDist_comm X' Y,
    ghpEDist_congr_left hY, ghpEDist_comm Y' X']

namespace MeasuredGHSpace
/-- Well-defined on whole-carrier measured-isometry classes. -/
noncomputable def edistance (x y : MeasuredGHSpace.{u}) : ℝ≥0∞ :=
  Quotient.liftOn₂ x y ghpEDist (fun _ _ _ _ hx hy ↦ ghpEDist_congr hx hy)

noncomputable def distance (x y : MeasuredGHSpace.{u}) : ℝ := (edistance x y).toReal

lemma edistance_mk (X Y : MeasuredCompact.{u}) :
    edistance (Quotient.mk _ X) (Quotient.mk _ Y) = ghpEDist X Y := rfl
end MeasuredGHSpace

/-- Exactly the manuscript's real infimum of max(Hausdorff, Prokhorov). -/
lemma ghpDist_eq_iInf (X Y : MeasuredCompact.{u}) :
    ghpDist X Y = ⨅ C : CompactCoupling X Y,
      max (hausdorffDist (range C.left) (range C.right))
        (levyProkhorovDist C.leftMeasure C.rightMeasure) := by
  rw [ghpDist, ghpEDist, ENNReal.toReal_iInf (fun C ↦ C.cost_ne_top)]
  congr 1
  funext C
  exact ENNReal.toReal_max
    (ne_top_of_le_ne_top C.cost_ne_top (le_max_left _ _))
    (levyProkhorovEDist_ne_top _ _)

theorem ghpBasic_spec : GHPBasicStatement.{u} :=
  ⟨ghpEDist_ne_top, ghpEDist_self, ghpEDist_comm,
    fun _ _ _ _ hx hy ↦ ghpEDist_congr hx hy, ghpDist_eq_iInf⟩
end PaperN.PartI
