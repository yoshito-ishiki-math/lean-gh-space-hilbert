import PaperN.PartI.IsometryGraphStatements
import PaperN.PartI.ValovInput

namespace PaperN.PartI
open TopologicalSpace MeasureTheory Filter
open scoped Topology
variable {Z : Type*} [MetricSpace Z]

def compactInclusion (K : NonemptyCompacts Z) : C(K, Z) :=
  ⟨Subtype.val, continuous_subtype_val⟩
def compactAction (K : NonemptyCompacts Z) (g : K ≃ᵢ K) : C(K, Z) :=
  ⟨fun x ↦ (g x : Z), continuous_subtype_val.comp g.continuous⟩

variable [MeasurableSpace Z] [BorelSpace Z]
/-- The entire manuscript `lem:isometry-limits`, including arbitrary laws along the
single selected graph subsequence. Probabilities have no full-support/invariance restriction. -/
def IsometryLimitsStatement : Prop :=
  ∀ (Ks : ℕ → NonemptyCompacts Z) (K : NonemptyCompacts Z),
    Tendsto Ks atTop (𝓝 K) → ∀ gs : ∀ n, Ks n ≃ᵢ Ks n,
      ∃ (φ : ℕ → ℕ) (g : K ≃ᵢ K), StrictMono φ ∧
        Tendsto (fun n ↦ isometryGraph (Ks (φ n)) (gs (φ n))) atTop (𝓝 (isometryGraph K g)) ∧
        ∀ (μs : ∀ n, ProbabilityMeasure (Ks (φ n))) (μ : ProbabilityMeasure K),
          Tendsto (fun n ↦ probabilityPushforward (compactInclusion (Ks (φ n))) (μs n))
            atTop (𝓝 (probabilityPushforward (compactInclusion K) μ)) →
          Tendsto (fun n ↦ probabilityPushforward (compactAction (Ks (φ n)) (gs (φ n))) (μs n))
            atTop (𝓝 (probabilityPushforward (compactAction K g) μ))

end PaperN.PartI
