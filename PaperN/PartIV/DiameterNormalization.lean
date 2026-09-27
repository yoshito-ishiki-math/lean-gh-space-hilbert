import PaperN.PartIV.UnitDiameterApproximation
import PaperN.Shared.Contraction

namespace PaperN.PartIV
open PaperN.Shared GromovHausdorff Set Metric
open scoped NNReal

/-- Diameter scales linearly, including the collapsed zero-scale quotient. -/
theorem ghDiameter_scaledGH (X : Type*) [MetricSpace X] [CompactSpace X] [Nonempty X]
    (a : ℝ≥0) : ghDiameter (scaledGH a X) = a.val * diam (univ : Set X) := by
  let d := (ContinuousPseudometric.ofMetric X).scale a
  change ghDiameter (toGHSpace d.Quotient) = _
  rw [ghDiameter_toGHSpace]
  have hd (x y : X) : dist (d.proj x) (d.proj y) = a.val * dist x y := d.dist_proj x y
  apply le_antisymm
  · apply diam_le_of_forall_dist_le (mul_nonneg a.coe_nonneg diam_nonneg)
    intro p _ q _
    obtain ⟨x,rfl⟩ := d.proj_surjective p
    obtain ⟨y,rfl⟩ := d.proj_surjective q
    rw [hd]
    exact mul_le_mul_of_nonneg_left
      (dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)) a.coe_nonneg
  · by_cases ha : a.val = 0
    · exact (mul_nonpos_of_nonpos_of_nonneg ha.le diam_nonneg).trans diam_nonneg
    · have hp : 0 < a.val := lt_of_le_of_ne a.coe_nonneg (Ne.symm ha)
      have hb : diam (univ : Set X) ≤ diam (univ : Set d.Quotient) / a.val := by
        apply diam_le_of_forall_dist_le (div_nonneg diam_nonneg a.coe_nonneg)
        intro x _ y _
        apply (le_div_iff₀ hp).mpr
        have h := dist_le_diam_of_mem (isCompact_univ : IsCompact (univ : Set d.Quotient)).isBounded
          (mem_univ (d.proj x)) (mem_univ (d.proj y))
        rw [hd] at h
        simpa only [mul_comm] using h
      have h := (le_div_iff₀ hp).mp hb
      simpa only [mul_comm] using h

/-- Scaling on GH classes has the expected diameter. -/
theorem ghDiameter_scaleGH (a : ℝ≥0) (q : GHSpace) :
    ghDiameter (scaleGH a q) = a.val * ghDiameter q := ghDiameter_scaledGH q.Rep a

/-- Positive-diameter classes form an open subspace. -/
theorem positiveDiameter_isOpen : IsOpen {q : GHSpace | 0 < ghDiameter q} :=
  isOpen_lt continuous_const ghDiameter_lipschitz.continuous

/-- Normalize every positive-diameter class to diameter one. -/
noncomputable def diameterNormalize (q : {q : GHSpace // 0 < ghDiameter q}) : UnitDiameterSpace :=
  ⟨scaleGH ⟨(ghDiameter q.val)⁻¹, inv_nonneg.mpr q.property.le⟩ q.val, by
    rw [ghDiameter_scaleGH]
    exact inv_mul_cancel₀ (ne_of_gt q.property)⟩

/-- Normalization is continuous throughout the positive-diameter locus. -/
theorem diameterNormalize_continuous : Continuous diameterNormalize := by
  have hd : Continuous (fun q : {q : GHSpace // 0 < ghDiameter q} ↦ ghDiameter q.val) :=
    ghDiameter_lipschitz.continuous.comp continuous_subtype_val
  have ha : Continuous (fun q : {q : GHSpace // 0 < ghDiameter q} ↦
      (⟨(ghDiameter q.val)⁻¹, inv_nonneg.mpr q.property.le⟩ : ℝ≥0)) :=
    (hd.inv₀ (fun q ↦ ne_of_gt q.property)).subtype_mk _
  exact (continuous_scaleGH.comp (continuous_subtype_val.prodMk ha)).subtype_mk _

/-- Normalization fixes every diameter-one class. -/
theorem diameterNormalize_retract (q : UnitDiameterSpace) :
    diameterNormalize ⟨q.val, by rw [q.property]; norm_num⟩ = q := by
  apply Subtype.ext
  change scaleGH _ q.val = q.val
  convert scaleGH_one q.val using 1
  apply congrArg (fun a ↦ scaleGH a q.val)
  apply Subtype.ext
  simp [q.property]

end PaperN.PartIV
