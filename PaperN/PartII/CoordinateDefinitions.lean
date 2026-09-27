import PaperN.Shared.Statements
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.RCLike.Real

namespace PaperN.PartII
open PaperN.Shared
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Coordinates with a continuous seminorm give a continuous pseudometric. -/
def coordinatePseudometric (p : Seminorm ℝ E) (hp : Continuous p) (f : C(X,E)) :
    ContinuousPseudometric X where
  kernel := ⟨fun z ↦ p (f z.1-f z.2), hp.comp ((f.continuous.comp continuous_fst).sub
    (f.continuous.comp continuous_snd))⟩
  self := by intro x; simp
  comm := by intro x y; exact map_sub_rev p _ _
  triangle := by
    intro x y z
    have he : f x-f z = (f x-f y)+(f y-f z) := by abel
    change p (f x-f z) ≤ p (f x-f y) + p (f y-f z)
    rw [he]
    exact map_add_le_add p _ _


noncomputable def coordinateBound (f : C(X,E)) : ℝ := ⨆ x, ‖f x‖
noncomputable def coordinateError (R : Correspondence X Y) (f : C(X,E)) (g : C(Y,E)) : ℝ :=
  ⨆ z : R.rel, ‖f z.val.1-g z.val.2‖
noncomputable def unitNormError (p q : Seminorm ℝ E) : ℝ :=
  ⨆ v : Metric.sphere (0 : E) 1, |p v - q v|
noncomputable def unitNormBound (q : Seminorm ℝ E) : ℝ :=
  ⨆ v : Metric.sphere (0 : E) 1, q v


theorem seminorm_continuous_finiteDimensional [FiniteDimensional ℝ E] (p : Seminorm ℝ E) :
    Continuous p := continuousOn_univ.mp (p.convexOn.continuousOn isOpen_univ)


universe u v
/-- Exact coordinate pseudometric estimate, with norms generalized to seminorms. -/
def CoordinatePseudometricEstimateStatement : Prop :=
  ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    (n : ℕ) [NeZero n]
    (R : Correspondence X Y)
    (p q : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (f : C(X,EuclideanSpace ℝ (Fin n))) (g : C(Y,EuclideanSpace ℝ (Fin n))),
    correspondenceError R
      (coordinatePseudometric p (seminorm_continuous_finiteDimensional p) f)
      (coordinatePseudometric q (seminorm_continuous_finiteDimensional q) g) ≤
      2 * coordinateBound f * unitNormError p q + 2 * unitNormBound q * coordinateError R f g

end PaperN.PartII
