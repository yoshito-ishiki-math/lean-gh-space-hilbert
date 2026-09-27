import PaperN.PartI.MeasuredProjection

namespace PaperN.PartI.CompactCoupling
open MeasureTheory Set Metric
universe u
variable {X Y : MeasuredCompact.{u}}

/-- A zero-cost realized coupling identifies whole carriers and their probabilities. -/
theorem isomorphic_of_cost_eq_zero (C : CompactCoupling X Y) (hc : C.cost = 0) :
    X.Isomorphic Y := by
  have hh : hausdorffEDist (range C.left) (range C.right) = 0 :=
    le_antisymm (hc ▸ le_max_left _ _) bot_le
  have hp : levyProkhorovEDist C.leftMeasure C.rightMeasure = 0 :=
    le_antisymm (hc ▸ le_max_right _ _) bot_le
  have hrange : range C.left = range C.right :=
    ((isCompact_range C.left_isometry.continuous).isClosed.hausdorffEDist_zero_iff
      (isCompact_range C.right_isometry.continuous).isClosed).mp hh
  let er : range C.left ≃ᵢ range C.right :=
    { toEquiv := Set.equivOfEq hrange, isometry_toFun := fun _ _ ↦ rfl }
  let e : X ≃ᵢ Y := C.left_isometry.isometryEquivOnRange.trans
    (er.trans C.right_isometry.isometryEquivOnRange.symm)
  have he : C.right ∘ e = C.left := by
    funext x
    have ht := C.right_isometry.isometryEquivOnRange.apply_symm_apply
      (er (C.left_isometry.isometryEquivOnRange x))
    exact congrArg Subtype.val ht
  let μ : ProbabilityMeasure C := ⟨C.leftMeasure,inferInstance⟩
  let ν : ProbabilityMeasure C := ⟨C.rightMeasure,inferInstance⟩
  have hd : dist (LevyProkhorov.ofMeasure μ) (LevyProkhorov.ofMeasure ν) = 0 := by
    change (levyProkhorovEDist C.leftMeasure C.rightMeasure).toReal = 0
    rw [hp]
    rfl
  have hm : C.leftMeasure = C.rightMeasure :=
    congrArg ProbabilityMeasure.toMeasure (congrArg LevyProkhorov.toMeasure (dist_eq_zero.mp hd))
  refine ⟨e, ?_⟩
  apply C.right_isometry.isClosedEmbedding.measurableEmbedding.map_injective
  rw [Measure.map_map C.right_isometry.continuous.measurable e.continuous.measurable, he]
  exact hm
end PaperN.PartI.CompactCoupling

namespace PaperN.PartI
open GromovHausdorff
universe u
/-- Zero GHP distance already identifies the whole underlying compact metric carriers. -/
theorem isometryEquiv_of_ghpDist_eq_zero (X Y : MeasuredCompact.{u}) (h : ghpDist X Y = 0) :
    Nonempty (X ≃ᵢ Y) := by
  have hd := MeasuredGHSpace.forget_distance_le (Quotient.mk _ X) (Quotient.mk _ Y)
  have hz : MeasuredGHSpace.distance (Quotient.mk _ X) (Quotient.mk _ Y) = 0 := h
  rw [hz] at hd
  have he := dist_eq_zero.mp (le_antisymm hd dist_nonneg)
  exact toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp he
end PaperN.PartI
