import PaperN.PartI.IsometryGraph
import Mathlib.Topology.UniformSpace.UniformApproximation

namespace PaperN.PartI
open Set Filter TopologicalSpace Metric
open scoped Topology

/-- Minima over Hausdorff-convergent compact sets converge when the functions converge uniformly.
The hypotheses record attainment and the lower-bound property, avoiding any infimum convention. -/
theorem compact_minima_tendsto {Z : Type*} [MetricSpace Z]
    (Ks : ℕ → NonemptyCompacts Z) (K : NonemptyCompacts Z)
    (hK : Tendsto Ks atTop (𝓝 K)) (fs : ℕ → Z → ℝ) (f : Z → ℝ)
    (hf : Continuous f) (hu : TendstoUniformly fs f atTop)
    (ms : ℕ → ℝ) (m : ℝ)
    (hs : ∀ n, (∃ x ∈ Ks n, fs n x = ms n) ∧ ∀ x ∈ Ks n, ms n ≤ fs n x)
    (hm : (∃ x ∈ K, f x = m) ∧ ∀ x ∈ K, m ≤ f x) :
    Tendsto ms atTop (𝓝 m) := by
  obtain ⟨x, hx, hfx⟩ := hm.1
  obtain ⟨xs, hxs, hxt⟩ := exists_tendsto_mem_compacts hK hx
  have hval := hu.tendsto_comp hf.continuousAt hxt
  rw [hfx] at hval
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let U : Set Z := {z | m - ε / 2 < f z}
  have hU : IsOpen U := isOpen_lt continuous_const hf
  have hKU : (K : Set Z) ⊆ U := fun z hz ↦ by
    change m - ε / 2 < f z
    linarith [hm.2 z hz]
  have hsets : ∀ᶠ n in atTop, (Ks n : Set Z) ⊆ U :=
    hK.eventually ((NonemptyCompacts.isOpen_subsets_of_isOpen hU).mem_nhds hKU)
  have herr := Metric.tendstoUniformly_iff.mp hu (ε / 2) (half_pos hε)
  have hupper := hval.eventually (gt_mem_nhds (show m < m + ε from by linarith))
  filter_upwards [hsets, herr, hupper] with n hn he hupp
  obtain ⟨y, hy, hfy⟩ := (hs n).1
  have hlo := hn hy
  change m - ε / 2 < f y at hlo
  have herr' := he y
  rw [Real.dist_eq, abs_sub_lt_iff] at herr'
  have hbound := (hs n).2 (xs n) (hxs n)
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith
end PaperN.PartI
