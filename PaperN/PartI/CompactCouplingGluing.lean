import PaperN.PartI.GHPDistance
import PaperN.PartI.ProkhorovIsometry

namespace PaperN.PartI.CompactCoupling
open Set Metric MeasureTheory
universe u
variable {X Y Z : MeasuredCompact.{u}}

/-- Compact union of the two ambient images in their metric gluing over Y. -/
def gluedCarrier (C : CompactCoupling X Y) (D : CompactCoupling Y Z) :=
  range (toGlueL C.right_isometry D.left_isometry) ∪
    range (toGlueR C.right_isometry D.left_isometry)

instance gluedCarrier_compactSpace (C : CompactCoupling X Y) (D : CompactCoupling Y Z) :
    CompactSpace (gluedCarrier C D) := by
  apply isCompact_iff_compactSpace.mp
  exact (isCompact_range (toGlueL_isometry C.right_isometry D.left_isometry).continuous).union
    (isCompact_range (toGlueR_isometry C.right_isometry D.left_isometry).continuous)

noncomputable def glueLeft (C : CompactCoupling X Y) (D : CompactCoupling Y Z) : C → gluedCarrier C D :=
  fun x ↦ ⟨toGlueL C.right_isometry D.left_isometry x,Or.inl ⟨x,rfl⟩⟩
noncomputable def glueRight (C : CompactCoupling X Y) (D : CompactCoupling Y Z) : D → gluedCarrier C D :=
  fun x ↦ ⟨toGlueR C.right_isometry D.left_isometry x,Or.inr ⟨x,rfl⟩⟩

theorem glueLeft_isometry (C : CompactCoupling X Y) (D : CompactCoupling Y Z) :
    Isometry (glueLeft C D) := by
  intro x y
  exact (toGlueL_isometry C.right_isometry D.left_isometry).edist_eq x y

theorem glueRight_isometry (C : CompactCoupling X Y) (D : CompactCoupling Y Z) :
    Isometry (glueRight C D) := by
  intro x y
  exact (toGlueR_isometry C.right_isometry D.left_isometry).edist_eq x y

theorem glue_commute (C : CompactCoupling X Y) (D : CompactCoupling Y Z) :
    glueLeft C D ∘ C.right = glueRight C D ∘ D.left := by
  funext y
  apply Subtype.ext
  exact congrFun (toGlue_commute C.right_isometry D.left_isometry) y

/-- Compose compact couplings by gluing along their common measured carrier. -/
noncomputable def trans (C : CompactCoupling X Y) (D : CompactCoupling Y Z) : CompactCoupling X Z where
  Carrier := gluedCarrier C D
  metric := inferInstance
  compact := inferInstance
  left := glueLeft C D ∘ C.left
  right := glueRight C D ∘ D.right
  left_isometry := (glueLeft_isometry C D).comp C.left_isometry
  right_isometry := (glueRight_isometry C D).comp D.right_isometry

/-- The composite coupling costs at most the sum of its two input costs. -/
theorem cost_trans_le (C : CompactCoupling X Y) (D : CompactCoupling Y Z) :
    (C.trans D).cost ≤ C.cost + D.cost := by
  letI : MeasurableSpace (gluedCarrier C D) := borel _
  letI : BorelSpace (gluedCarrier C D) := ⟨rfl⟩
  have hL := glueLeft_isometry C D
  have hR := glueRight_isometry C D
  have hm : Measure.map (glueLeft C D) C.rightMeasure =
      Measure.map (glueRight C D) D.leftMeasure := by
    unfold rightMeasure leftMeasure
    rw [Measure.map_map hL.continuous.measurable C.right_isometry.continuous.measurable,
      Measure.map_map hR.continuous.measurable D.left_isometry.continuous.measurable, glue_commute]
  have hh : hausdorffEDist (range ((C.trans D).left)) (range ((C.trans D).right)) ≤
      hausdorffEDist (range C.left) (range C.right) + hausdorffEDist (range D.left) (range D.right) := by
    have ht := hausdorffEDist_triangle (s := range (glueLeft C D ∘ C.left))
      (t := range (glueLeft C D ∘ C.right)) (u := range (glueRight C D ∘ D.right))
    rw [show hausdorffEDist (range (glueLeft C D ∘ C.left)) (range (glueLeft C D ∘ C.right)) =
      hausdorffEDist (range C.left) (range C.right) by
        rw [range_comp,range_comp,hausdorffEDist_image hL],
      glue_commute] at ht
    simp only [range_comp] at ht
    rw [hausdorffEDist_image hR] at ht
    convert ht using 1 <;> simp only [trans, range_comp] <;> rfl
  have hp : levyProkhorovEDist (C.trans D).leftMeasure (C.trans D).rightMeasure ≤
      levyProkhorovEDist C.leftMeasure C.rightMeasure + levyProkhorovEDist D.leftMeasure D.rightMeasure := by
    have ht := levyProkhorovEDist_triangle (Measure.map (glueLeft C D) C.leftMeasure)
      (Measure.map (glueLeft C D) C.rightMeasure) (Measure.map (glueRight C D) D.rightMeasure)
    rw [levyProkhorovEDist_map_isometry _ hL,hm,levyProkhorovEDist_map_isometry _ hR] at ht
    change levyProkhorovEDist (Measure.map (glueLeft C D ∘ C.left) X.measure)
      (Measure.map (glueRight C D ∘ D.right) Z.measure) ≤ _
    rw [← Measure.map_map hL.continuous.measurable C.left_isometry.continuous.measurable,
      ← Measure.map_map hR.continuous.measurable D.right_isometry.continuous.measurable]
    exact ht
  apply max_le
  · exact hh.trans (add_le_add (le_max_left _ _) (le_max_left _ _))
  · exact hp.trans (add_le_add (le_max_right _ _) (le_max_right _ _))
end PaperN.PartI.CompactCoupling

namespace PaperN.PartI
universe u
/-- Triangle inequality for the max-convention extended GHP infimum. -/
theorem ghpEDist_triangle (X Y Z : MeasuredCompact.{u}) :
    ghpEDist X Z ≤ ghpEDist X Y + ghpEDist Y Z := by
  apply ENNReal.le_iInf_add_iInf
  intro C D
  exact (iInf_le _ (C.trans D)).trans (C.cost_trans_le D)

/-- Triangle inequality for the real GHP distance. -/
theorem ghpDist_triangle (X Y Z : MeasuredCompact.{u}) :
    ghpDist X Z ≤ ghpDist X Y + ghpDist Y Z := by
  have h := ENNReal.toReal_mono (by simp [ghpEDist_ne_top]) (ghpEDist_triangle X Y Z)
  simpa [ghpDist, ENNReal.toReal_add, ghpEDist_ne_top] using h

/-- The triangle inequality descends to measured isometry classes. -/
theorem MeasuredGHSpace.distance_triangle (x y z : MeasuredGHSpace.{u}) :
    MeasuredGHSpace.distance x z ≤ MeasuredGHSpace.distance x y + MeasuredGHSpace.distance y z := by
  refine Quotient.inductionOn₃ x y z ?_
  intro X Y Z
  exact ghpDist_triangle X Y Z
end PaperN.PartI
