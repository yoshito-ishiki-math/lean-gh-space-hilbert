import PaperN.PartII.ComplexSymmetry

namespace PaperN.PartII

/-- A symmetric operator has no nonzero vector killed only by its square. -/
theorem symmetric_apply_apply_eq_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (hs : T.toLinearMap.IsSymmetric) (x : H)
    (hx : T (T x) = 0) : T x = 0 := by
  have hh := hs x (T x)
  change inner ℂ (T x) (T x) = inner ℂ x (T (T x)) at hh
  rw [hx, inner_zero_right] at hh
  exact inner_self_eq_zero.mp hh

/-- For SR with RS symmetric, R is injective on the range of (SR) squared. -/
theorem factor_restriction_zero_on_square_range
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S : H →L[ℂ] E) (R : E →L[ℂ] H)
    (hs : (R.comp S).toLinearMap.IsSymmetric)
    (x : E) (hx : x ∈ LinearMap.range ((S.comp R).comp (S.comp R)).toLinearMap)
    (hr : R x = 0) : x = 0 := by
  obtain ⟨y,hy⟩ := hx
  change S (R (S (R y))) = x at hy
  have hz : (R.comp S) ((R.comp S) (R y)) = 0 := by
    change R (S (R (S (R y)))) = 0
    rw [hy,hr]
  have hh := symmetric_apply_apply_eq_zero (R.comp S) hs (R y) hz
  change R (S (R y)) = 0 at hh
  rw [← hy,hh,map_zero]

namespace AmbientKernel
open MeasureTheory
universe u v
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Z : Type v} [MetricSpace Z] [CompactSpace Z]
variable (e : C(X,Z)) (μ : Measure X) [IsProbabilityMeasure μ]

/-- Restriction detects zero on the squared ambient kernel range. -/
theorem restriction_zero_on_ambient_square_range (he : Isometry e)
    (f : C(Z,ℂ))
    (hf : f ∈ LinearMap.range ((ambientOperator e μ).comp (ambientOperator e μ)).toLinearMap)
    (hr : restriction e μ f = 0) : f = 0 := by
  apply factor_restriction_zero_on_square_range (distanceToContinuous e μ) (restriction e μ) _ f hf hr
  change ((restriction e μ).comp (distanceToContinuous e μ)).toLinearMap.IsSymmetric
  rw [restriction_extension e μ he]
  exact ComplexKernel.distanceOperator_symmetric μ
end AmbientKernel
end PaperN.PartII
