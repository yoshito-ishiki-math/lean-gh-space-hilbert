import PaperN.PartI.FullSupportStatements

namespace PaperN.PartI
open Set TopologicalSpace
universe u
namespace MeasuredGHSpace

/-- The countable positivity conditions characterize full support on the quotient. -/
theorem fullSupport_iff_minimumMass_pos (q : MeasuredGHSpace.{u}) :
    q.fullSupport ↔ ∀ n : ℕ, 0 < minimumMass ((1 / 2 : ℝ) ^ n) q := by
  refine Quotient.inductionOn q ?_
  intro X
  exact support_eq_univ_iff_minimumBallMass_pos X.probability

/-- An explicit countable intersection of open minimum-mass conditions. -/
theorem fullSupport_eq_iInter :
    {q : MeasuredGHSpace.{u} | q.fullSupport} =
      ⋂ n : ℕ, {q | 0 < minimumMass ((1 / 2 : ℝ) ^ n) q} := by
  ext q
  simp only [mem_setOf_eq, mem_iInter]
  exact fullSupport_iff_minimumMass_pos q
end MeasuredGHSpace

/-- Full-support classes form a Gδ in varying GHP space, conditional only on the
previously identified metric and common-embedding literature inputs. -/
theorem fullSupportGDelta_spec (hm : GHPMetricInput.{u}) (hc : GHPCommonEmbeddingInput.{u}) :
    FullSupportGDeltaStatement hm := by
  letI := hm.metricSpace
  change IsGδ {q : MeasuredGHSpace.{u} | q.fullSupport}
  rw [MeasuredGHSpace.fullSupport_eq_iInter]
  apply IsGδ.iInter_of_isOpen
  intro n
  exact isOpen_lt continuous_const (MeasuredGHSpace.continuous_minimumMass hm hc _)
end PaperN.PartI
