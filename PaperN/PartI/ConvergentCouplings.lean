import PaperN.PartI.ZeroDistanceCouplings

namespace PaperN.PartI
open Filter
open scoped Topology
universe u

/-- Choose a compact realization within any positive error of the GHP infimum. -/
theorem exists_coupling_cost_lt (X Y : MeasuredCompact.{u}) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : CompactCoupling X Y, C.cost.toReal < ghpDist X Y + ε := by
  have hn : 0 ≤ ghpDist X Y := ENNReal.toReal_nonneg
  have hi : ghpEDist X Y < ENNReal.ofReal (ghpDist X Y + ε) := by
    calc
      ghpEDist X Y = ENNReal.ofReal (ghpDist X Y) :=
        (ENNReal.ofReal_toReal (ghpEDist_ne_top X Y)).symm
      _ < _ := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hn).mpr (by linarith)
  obtain ⟨C, hC⟩ := iInf_lt_iff.mp hi
  exact ⟨C, ENNReal.toReal_lt_of_lt_ofReal hC⟩

/-- GHP convergence supplies prescribed couplings of vanishing cost. -/
theorem exists_couplings_cost_tendsto (X : MeasuredCompact.{u})
    (Ys : ℕ → MeasuredCompact.{u})
    (h : Tendsto (fun n ↦ ghpDist X (Ys n)) atTop (𝓝 0)) :
    ∃ C : ∀ n, CompactCoupling X (Ys n),
      Tendsto (fun n ↦ (C n).cost.toReal) atTop (𝓝 0) := by
  have he (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
  choose C hC using fun n ↦ exists_coupling_cost_lt X (Ys n) (he n)
  refine ⟨C, squeeze_zero (fun _ ↦ ENNReal.toReal_nonneg) (fun n ↦ (hC n).le) ?_⟩
  simpa only [add_zero] using h.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
end PaperN.PartI
