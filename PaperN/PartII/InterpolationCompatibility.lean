import PaperN.PartII.InterpolationContinuity

namespace PaperN.Shared.ContinuousPseudometric
universe u
variable {X : Type u} [MetricSpace X]

/-- The original distance survives with weight `1-t`. -/
theorem blend_ofMetric_lower (d : ContinuousPseudometric X)
    (t : Set.Icc (0 : ℝ) 1) (x y : X) :
    (1 - t.val) * dist x y ≤ ((ofMetric X).blend d t) x y := by
  change (1 - t.val) * dist x y ≤ (1 - t.val) * dist x y + t.val * d x y
  exact le_add_of_nonneg_right (mul_nonneg t.property.1 (d.nonneg x y))

/-- Before the last time, the interpolation separates points. -/
theorem blend_ofMetric_eq_zero_iff (d : ContinuousPseudometric X)
    (t : Set.Icc (0 : ℝ) 1) (ht : t.val < 1) (x y : X) :
    ((ofMetric X).blend d t) x y = 0 ↔ x = y := by
  constructor
  · intro h
    have hle := blend_ofMetric_lower d t x y
    rw [h] at hle
    have hp : 0 < 1 - t.val := sub_pos.mpr ht
    have : dist x y ≤ 0 := by nlinarith
    exact dist_le_zero.mp this
  · rintro rfl
    exact ((ofMetric X).blend d t).self x

/-- The actual quotient projection is a homeomorphism, for the original topology. -/
noncomputable def blendOfMetricHomeomorph [CompactSpace X]
    (d : ContinuousPseudometric X) (t : Set.Icc (0 : ℝ) 1) (ht : t.val < 1) :
    X ≃ₜ ((ofMetric X).blend d t).Quotient :=
  (Equiv.ofBijective ((ofMetric X).blend d t).proj
    ⟨fun x y h ↦ (blend_ofMetric_eq_zero_iff d t ht x y).mp
      ((((ofMetric X).blend d t).proj_eq_iff x y).mp h),
      ((ofMetric X).blend d t).proj_surjective⟩).toHomeomorphOfContinuousClosed
    ((ofMetric X).blend d t).continuous_proj
    ((ofMetric X).blend d t).continuous_proj.isClosedMap

/-- The homeomorphism realizes precisely the interpolated distance. -/
theorem blendOfMetricHomeomorph_dist [CompactSpace X]
    (d : ContinuousPseudometric X) (t : Set.Icc (0 : ℝ) 1) (ht : t.val < 1)
    (x y : X) :
    dist (blendOfMetricHomeomorph d t ht x) (blendOfMetricHomeomorph d t ht y) =
      (1 - t.val) * dist x y + t.val * d x y :=
  ((ofMetric X).blend d t).dist_proj x y

end PaperN.Shared.ContinuousPseudometric

namespace PaperN.PartII
open PaperN.Shared PaperN.PartI

/-- Every chosen global model has the original compact topology before time one. -/
theorem modelInterpolation_compatible
    {A : ℕ → MeasuredCompact.{0}} {τ : ℕ → ℝ}
    (M : ∀ i, LocalModel (A i) (τ i))
    (ρ : PartitionOfUnity ℕ GromovHausdorff.GHSpace)
    (X : MeasuredCompact.{0}) (t : Set.Icc (0 : ℝ) 1) (ht : t.val < 1) :
    ∃ h : X ≃ₜ ((ContinuousPseudometric.ofMetric X).blend
        (modelPseudometric M ρ X) t).Quotient,
      ∀ x y, dist (h x) (h y) =
        (1 - t.val) * dist x y + t.val * modelPseudometric M ρ X x y := by
  exact ⟨ContinuousPseudometric.blendOfMetricHomeomorph _ t ht,
    ContinuousPseudometric.blendOfMetricHomeomorph_dist _ t ht⟩

end PaperN.PartII
