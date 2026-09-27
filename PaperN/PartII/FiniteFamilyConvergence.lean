import PaperN.PartII.CorrespondenceFunctionConvergence

namespace PaperN.PartII
open Filter
open scoped Topology

theorem finite_family_norm_tendsto {ι E : Type*} [Finite ι] [Nonempty ι]
    [NormedAddCommGroup E] (fs : ℕ → ι → E) (f : ι → E)
    (hf : ∀ i, Tendsto (fun n ↦ fs n i) atTop (𝓝 (f i))) :
    Tendsto (fun n ↦ ⨆ i, ‖fs n i - f i‖) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hh : ∀ᶠ n in atTop, ∀ i, dist (fs n i) (f i) < ε / 2 :=
    Filter.eventually_all.mpr fun i ↦ Metric.tendsto_nhds.mp (hf i) (ε / 2) (half_pos hε)
  filter_upwards [hh] with n hn
  have hb : BddAbove (Set.range (fun i ↦ ‖fs n i - f i‖)) := (Set.finite_range _).bddAbove
  have hlo : 0 ≤ ⨆ i, ‖fs n i - f i‖ :=
    (norm_nonneg _).trans (le_ciSup hb (Classical.choice inferInstance))
  have hhi : (⨆ i, ‖fs n i - f i‖) ≤ ε / 2 :=
    ciSup_le fun i ↦ by simpa only [dist_eq_norm] using (hn i).le
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hlo] using hhi.trans_lt (half_lt_self hε)

end PaperN.PartII
