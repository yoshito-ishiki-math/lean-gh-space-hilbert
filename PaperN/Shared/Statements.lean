import PaperN.Shared.ContinuousPseudometric
import Mathlib.Data.Set.Card
import Mathlib.Topology.Homotopy.Contractible

namespace PaperN.Shared
open Set Metric GromovHausdorff Filter
open scoped NNReal Topology
universe u v

/-- cor:uniform-separated-sets, for arbitrary (possibly initially infinite) separated subsets. -/
def UniformSeparatedStatement : Prop :=
  ∀ (Xs : ℕ → Type u) (X : Type v)
    [∀ n, MetricSpace (Xs n)] [∀ n, CompactSpace (Xs n)] [∀ n, Nonempty (Xs n)]
    [MetricSpace X] [CompactSpace X] [Nonempty X],
    Tendsto (fun n ↦ toGHSpace (Xs n)) atTop (𝓝 (toGHSpace X)) →
    ∀ ε > 0, ∃ N : ℕ, 0 < N ∧ ∀ n (S : Set (Xs n)),
      S.Pairwise (fun x y ↦ ε ≤ dist x y) → S.Finite ∧ S.ncard ≤ N

section Pseudometrics
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]

noncomputable def correspondenceError (R : Correspondence X Y)
    (d : ContinuousPseudometric X) (e : ContinuousPseudometric Y) : ℝ :=
  ⨆ z : R.rel × R.rel, |d z.1.val.1 z.2.val.1 - e z.1.val.2 z.2.val.2|

end Pseudometrics

/-- All four conclusions of lem:pseudometric-comparison, on arbitrary compact topological carriers. -/
def PseudometricComparisonStatement : Prop :=
  ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    (R : Correspondence X Y) (d₀ d₁ : ContinuousPseudometric X)
    (e₀ e₁ : ContinuousPseudometric Y),
    ghDist d₀.Quotient e₀.Quotient ≤ correspondenceError R d₀ e₀ / 2 ∧
    |‖d₀.kernel-d₁.kernel‖ - ‖e₀.kernel-e₁.kernel‖| ≤
      correspondenceError R d₀ e₀ + correspondenceError R d₁ e₁ ∧
    (∀ t : Set.Icc (0 : ℝ) 1,
      correspondenceError R (d₀.blend d₁ t) (e₀.blend e₁ t) ≤
      (1-t.val)*correspondenceError R d₀ e₀+t.val*correspondenceError R d₁ e₁) ∧
    ghDist d₀.Quotient d₁.Quotient ≤ ‖d₀.kernel-d₁.kernel‖ / 2

noncomputable def scaledGH (a : ℝ≥0) (X : Type u) [MetricSpace X]
    [CompactSpace X] [Nonempty X] : GHSpace :=
  ((ContinuousPseudometric.ofMetric X).scale a).gh

noncomputable def scaleGH (a : ℝ≥0) (q : GHSpace) : GHSpace := scaledGH a q.Rep

noncomputable def pointGH : GHSpace := toGHSpace Unit

noncomputable def contraction (q : GHSpace) (t : Set.Icc (0 : ℝ) 1) : GHSpace :=
  scaleGH ⟨1-t.val, sub_nonneg.mpr t.property.2⟩ q


/-- The quantitative part of lem:scaling-contraction. -/
def ScalingStatement : Prop :=
  ∀ (X : Type u) (Y : Type v) [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y] (a b : ℝ≥0),
    dist (scaledGH a X) (scaledGH b Y) ≤
      (a : ℝ)*ghDist X Y + |(a : ℝ)-b|/2 * diam (univ : Set Y)

/-- Representative independence, continuity, both endpoints, fixed point, and contractibility. -/
def ContractionStatement : Prop :=
  (∀ (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
    (t : Set.Icc (0 : ℝ) 1), contraction (toGHSpace X) t =
      scaledGH ⟨1-t.val, sub_nonneg.mpr t.property.2⟩ X) ∧
  Continuous (fun p : GHSpace × Set.Icc (0 : ℝ) 1 ↦ contraction p.1 p.2) ∧
  (∀ q, contraction q ⟨0,by norm_num⟩ = q) ∧
  (∀ q, contraction q ⟨1,by norm_num⟩ = pointGH) ∧
  (∀ t, contraction pointGH t = pointGH) ∧ ContractibleSpace GHSpace
end PaperN.Shared
