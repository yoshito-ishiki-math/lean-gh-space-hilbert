import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.Normed.Module.FiniteDimension

import PaperN.PartII.MinimizerContinuityStatements

namespace PaperN.PartII
open Set Filter Topology

/-- Uniform convergence on compact sets and bounded minimizers imply convergence
when the limiting objective has a unique global minimizer. The proper metric
version also covers every finite-dimensional real normed space. -/
theorem minimizer_tendsto {E : Type*} [MetricSpace E] [ProperSpace E]
    (F : ℕ → E → ℝ) (f : E → ℝ) (u : ℕ → E) (a : E)
    (hf : Continuous f)
    (hu : ∀ K : Set E, IsCompact K → TendstoUniformlyOn F f atTop K)
    (hb : Bornology.IsBounded (range u))
    (hm : ∀ n x, F n (u n) ≤ F n x)
    (hunique : ∀ x, (∀ y, f x ≤ f y) → x = a) :
    Tendsto u atTop (𝓝 a) := by
  have hK := hb.isCompact_closure
  apply hK.tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall fun n ↦ subset_closure (mem_range_self n))
  intro x hx hcluster
  obtain ⟨φ,hφ,hlim⟩ := hcluster.tendsto_subseq
  apply hunique x
  intro y
  have hsub : TendstoUniformlyOn (fun n ↦ F (φ n)) f atTop (closure (range u)) :=
    fun V hV ↦ hφ.tendsto_atTop.eventually (hu _ hK V hV)
  have hwithin : Tendsto (u ∘ φ) atTop (𝓝[closure (range u)] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall
      (fun n ↦ subset_closure (mem_range_self (φ n)))⟩
  have hvalues := hsub.tendsto_comp hf.continuousAt.continuousWithinAt hwithin
  have hcompetitor := ((hu {y} (isCompact_singleton)).tendsto_at (mem_singleton y)).comp
    hφ.tendsto_atTop
  exact le_of_tendsto_of_tendsto hvalues hcompetitor (Eventually.of_forall fun n ↦ hm (φ n) y)

theorem minimizerContinuity_spec : MinimizerContinuityStatement := by
  intro n _ F f u a _ hf hu hb hm _ hunique
  exact minimizer_tendsto F f u a hf hu hb hm hunique

end PaperN.PartII
