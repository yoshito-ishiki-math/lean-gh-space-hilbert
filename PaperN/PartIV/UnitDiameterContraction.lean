import PaperN.PartIV.ProductDiameter

set_option backward.isDefEq.respectTransparency false

namespace PaperN.PartIV
open PaperN.Shared GromovHausdorff Set
open scoped NNReal

/-- Oppositely scaled factors always have a positive-diameter max product. -/
theorem unitDiameter_product_positive (q d : UnitDiameterSpace) (t : Icc (0 : ℝ) 1) :
    0 < ghDiameter (productGH
      (scaleGH ⟨1-t.val, sub_nonneg.mpr t.property.2⟩ q.val)
      (scaleGH ⟨t.val, t.property.1⟩ d.val)) := by
  rw [ghDiameter_productGH, ghDiameter_scaleGH, ghDiameter_scaleGH, q.property, d.property]
  simp only [mul_one]
  by_cases h : t.val ≤ 0
  · exact lt_of_lt_of_le (by linarith : 0 < 1-t.val) (le_max_left _ _)
  · exact lt_of_lt_of_le (lt_of_not_ge h) (le_max_right _ _)

/-- Contract toward any fixed unit-diameter space by normalized scaled products. -/
noncomputable def unitDiameterContraction (d q : UnitDiameterSpace) (t : Icc (0 : ℝ) 1) :
    UnitDiameterSpace :=
  diameterNormalize ⟨productGH
    (scaleGH ⟨1-t.val, sub_nonneg.mpr t.property.2⟩ q.val)
    (scaleGH ⟨t.val, t.property.1⟩ d.val), unitDiameter_product_positive q d t⟩

/-- The normalized product homotopy is jointly continuous. -/
theorem unitDiameterContraction_continuous (d : UnitDiameterSpace) :
    Continuous (fun p : UnitDiameterSpace × Icc (0 : ℝ) 1 ↦ unitDiameterContraction d p.1 p.2) := by
  have ht : Continuous (fun p : UnitDiameterSpace × Icc (0 : ℝ) 1 ↦ p.2.val) :=
    continuous_subtype_val.comp continuous_snd
  have h₁ : Continuous (fun p : UnitDiameterSpace × Icc (0 : ℝ) 1 ↦
      (⟨1-p.2.val, sub_nonneg.mpr p.2.property.2⟩ : ℝ≥0)) :=
    (continuous_const.sub ht).subtype_mk _
  have h₂ : Continuous (fun p : UnitDiameterSpace × Icc (0 : ℝ) 1 ↦
      (⟨p.2.val, p.2.property.1⟩ : ℝ≥0)) := ht.subtype_mk _
  have hf := continuous_scaleGH.comp ((continuous_subtype_val.comp continuous_fst).prodMk h₁)
  have hg := continuous_scaleGH.comp ((continuous_const (y := d.val)).prodMk h₂)
  exact diameterNormalize_continuous.comp
    ((productGH_lipschitz.continuous.comp (hf.prodMk hg)).subtype_mk _)

/-- Initial endpoint is the original unit-diameter space. -/
theorem unitDiameterContraction_zero (d q : UnitDiameterSpace) :
    unitDiameterContraction d q ⟨0, by norm_num⟩ = q := by
  have h : (⟨1-(0:ℝ), by norm_num⟩ : NNReal) = (1 : NNReal) := by apply Subtype.ext; norm_num
  have he : productGH (scaleGH ⟨1-(0:ℝ), by norm_num⟩ q.val)
      (scaleGH 0 d.val) = q.val := by rw [h, scaleGH_one, scaleGH_zero, productGH_point_right]
  unfold unitDiameterContraction
  convert diameterNormalize_retract q using 1
  apply congrArg diameterNormalize
  exact Subtype.ext he

/-- Final endpoint is the chosen fixed space. -/
theorem unitDiameterContraction_one (d q : UnitDiameterSpace) :
    unitDiameterContraction d q ⟨1, by norm_num⟩ = d := by
  have h : (⟨1-(1:ℝ), by norm_num⟩ : NNReal) = (0 : NNReal) := by apply Subtype.ext; norm_num
  have he : productGH (scaleGH ⟨1-(1:ℝ), by norm_num⟩ q.val)
      (scaleGH 1 d.val) = d.val := by rw [h, scaleGH_zero, scaleGH_one, productGH_point_left]
  unfold unitDiameterContraction
  convert diameterNormalize_retract d using 1
  apply congrArg diameterNormalize
  exact Subtype.ext he

attribute [local irreducible] unitDiameterContraction

/-- The unit-diameter subspace is contractible. -/
theorem unitDiameter_contractible : ContractibleSpace UnitDiameterSpace := by
  obtain ⟨d⟩ := unitDiameter_nonempty
  apply (contractible_iff_id_nullhomotopic UnitDiameterSpace).mpr
  refine ⟨d, ⟨?_⟩⟩
  refine {
    toFun := fun p ↦ unitDiameterContraction d p.2 p.1
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_ }
  · change Continuous (fun p : Icc (0 : ℝ) 1 × UnitDiameterSpace ↦
      unitDiameterContraction d p.2 p.1)
    exact (unitDiameterContraction_continuous d).comp
      (show Continuous (Prod.swap : Icc (0 : ℝ) 1 × UnitDiameterSpace →
        UnitDiameterSpace × Icc (0 : ℝ) 1) from continuous_swap)
  · intro q
    exact unitDiameterContraction_zero d q
  · intro q
    exact unitDiameterContraction_one d q

end PaperN.PartIV
