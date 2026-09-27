import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.TotallyBounded
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace PaperN.PartII
open Set MeasureTheory

/-- Probability integrals with values in a fixed compact set lie in one compact set. -/
theorem compact_probability_integral_container
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hK : IsCompact K) :
    ∃ L : Set E, IsCompact L ∧ ∀ {α : Type*} [MeasurableSpace α]
      (μ : Measure α) [IsProbabilityMeasure μ] (f : α → E),
      Integrable f μ → (∀ᵐ x ∂μ, f x ∈ K) → (∫ x, f x ∂μ) ∈ L := by
  refine ⟨closure (convexHull ℝ K), ?_, ?_⟩
  · exact isCompact_iff_totallyBounded_isComplete.mpr
      ⟨(totallyBounded_convexHull E hK.totallyBounded).closure, isClosed_closure.isComplete⟩
  · intro α _ μ _ f hf hm
    apply (convex_convexHull ℝ K).closure.integral_mem isClosed_closure _ hf
    exact hm.mono (fun x hx ↦ subset_closure (subset_convexHull ℝ K hx))

/-- The probability integral statement specialized to the unit parameter interval. -/
theorem compact_unit_interval_integral_container
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hK : IsCompact K) :
    ∃ L : Set E, IsCompact L ∧ ∀ f : ℝ → E,
      IntervalIntegrable f volume 0 1 → (∀ t ∈ Icc (0 : ℝ) 1, f t ∈ K) →
      (∫ t in (0 : ℝ)..1, f t) ∈ L := by
  obtain ⟨L,hL,hm⟩ := compact_probability_integral_container K hK
  refine ⟨L,hL,fun f hf hfK ↦ ?_⟩
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  haveI : IsProbabilityMeasure μ := ⟨by simp [μ]⟩
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply hm μ f
  · exact hf.1
  · apply (ae_restrict_mem measurableSet_Ioc).mono
    intro t ht
    exact hfK t ⟨ht.1.le, ht.2⟩
end PaperN.PartII
