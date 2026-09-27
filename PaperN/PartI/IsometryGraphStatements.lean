import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Sequences
import Mathlib.Tactic

namespace PaperN.PartI
open TopologicalSpace Set Filter
open scoped Topology
variable {Z : Type*} [MetricSpace Z]

/-- The graph, in the ambient maximum product metric, of an onto isometry of K. -/
noncomputable def isometryGraph (K : NonemptyCompacts Z) (g : K ≃ᵢ K) :
    NonemptyCompacts (Z × Z) :=
  (⊤ : NonemptyCompacts K).map (fun x : K ↦ ((x : Z), (g x : Z))) (by fun_prop)

/-- The graph-subsequence conclusion of `lem:isometry-limits` only.
The additional convergence-of-pushforwards assertion is not included here. -/
def IsometryGraphSubsequenceStatement : Prop :=
  ∀ (Ks : ℕ → NonemptyCompacts Z) (K : NonemptyCompacts Z),
    Tendsto Ks atTop (𝓝 K) → ∀ gs : ∀ n, Ks n ≃ᵢ Ks n,
      ∃ (φ : ℕ → ℕ) (g : K ≃ᵢ K), StrictMono φ ∧
        Tendsto (fun n ↦ isometryGraph (Ks (φ n)) (gs (φ n))) atTop (𝓝 (isometryGraph K g))

end PaperN.PartI
