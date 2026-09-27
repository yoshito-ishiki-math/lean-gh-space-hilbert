import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.UniformSpace.UniformConvergence

namespace PaperN.PartII
open Set Filter Topology

/-- Exact Euclidean statement of lem:minimizer-continuity. -/
def MinimizerContinuityStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (F : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (u : ℕ → EuclideanSpace ℝ (Fin n))
    (a : EuclideanSpace ℝ (Fin n)),
    (∀ k, Continuous (F k)) → Continuous f →
    (∀ K, IsCompact K → TendstoUniformlyOn F f atTop K) →
    Bornology.IsBounded (range u) → (∀ k x, F k (u k) ≤ F k x) →
    (∀ y, f a ≤ f y) → (∀ x, (∀ y, f x ≤ f y) → x = a) →
    Tendsto u atTop (𝓝 a)
end PaperN.PartII
