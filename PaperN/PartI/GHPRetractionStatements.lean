import PaperN.PartI.GHPExternalStatements
import PaperN.PartI.FullSupportStatements
import Mathlib.Topology.Homeomorph.Defs

namespace PaperN.PartI
open GromovHausdorff Set Topology
universe u

/-- `cor:ghp-retract` in any universe model. The same image is a retract of every
subspace containing it, in particular the full-support and invariant-full-support subspaces. -/
def GHPRetractionStatement (hm : GHPMetricInput.{u}) : Prop :=
  letI := hm.metricSpace
  ∃ s : C(GHSpace, MeasuredGHSpace.{u}),
    Function.LeftInverse MeasuredGHSpace.forget s ∧ IsEmbedding s ∧
    (∀ q, (s q).invariantFullSupport ∧ (s q).fullSupport) ∧
    Nonempty (GHSpace ≃ₜ range s) ∧
    (∃ r : C(MeasuredGHSpace.{u}, range s), ∀ x : range s, r x.val = x) ∧
    ∀ (S : Set MeasuredGHSpace.{u}) (hS : range s ⊆ S),
      ∃ r : C(S, range s), ∀ x : range s, r ⟨x.val, hS x.property⟩ = x
end PaperN.PartI
