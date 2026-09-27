import PaperN.PartI.GHPDistance
import Mathlib.Analysis.SpecificLimits.Basic

namespace PaperN.PartI
open Filter Metric MeasureTheory Set
open scoped Topology
universe u

/-- A zero GHP infimum supplies compact realizations of arbitrarily small cost. -/
theorem exists_coupling_cost_lt_of_ghpDist_eq_zero
    (X Y : MeasuredCompact.{u}) (h : ghpDist X Y = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : CompactCoupling X Y, C.cost.toReal < ε := by
  have hz : ghpEDist X Y = 0 := by
    simpa [ghpDist, ENNReal.toReal_eq_zero_iff, ghpEDist_ne_top] using h
  have hi : ghpEDist X Y < ENNReal.ofReal ε := by
    rw [hz]
    exact ENNReal.ofReal_pos.mpr hε
  obtain ⟨C, hC⟩ := iInf_lt_iff.mp hi
  exact ⟨C, ENNReal.toReal_lt_of_lt_ofReal hC⟩

/-- The two parts of the max-cost vanish along a sequence of compact couplings.
The ambient carrier may depend on the index; no common-ambient limit is asserted. -/
theorem exists_couplings_tendsto_zero_of_ghpDist_eq_zero
    (X Y : MeasuredCompact.{u}) (h : ghpDist X Y = 0) :
    ∃ C : ℕ → CompactCoupling X Y,
      Tendsto (fun n ↦ (C n).cost.toReal) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ (hausdorffEDist (range (C n).left)
        (range (C n).right)).toReal) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ (levyProkhorovEDist (C n).leftMeasure
        (C n).rightMeasure).toReal) atTop (𝓝 0) := by
  have he (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
  choose C hC using fun n ↦ exists_coupling_cost_lt_of_ghpDist_eq_zero X Y h (he n)
  have ht : Tendsto (fun n ↦ (C n).cost.toReal) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ ENNReal.toReal_nonneg)
      (fun n ↦ (hC n).le) (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine ⟨C, ht, ?_, ?_⟩
  · exact squeeze_zero (fun _ ↦ ENNReal.toReal_nonneg)
      (fun n ↦ ENNReal.toReal_mono (C n).cost_ne_top (le_max_left _ _)) ht
  · exact squeeze_zero (fun _ ↦ ENNReal.toReal_nonneg)
      (fun n ↦ ENNReal.toReal_mono (C n).cost_ne_top (le_max_right _ _)) ht
end PaperN.PartI
