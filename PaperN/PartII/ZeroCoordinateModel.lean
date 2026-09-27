import PaperN.PartII.CoordinatePullback
import PaperN.PartII.MetricApproximationError

namespace PaperN.PartII
open PaperN.Shared Metric Set

/-- The fixed one-dimensional coordinate model used around singleton spaces. -/
noncomputable def zeroCoordinatePair (X : Type*) [TopologicalSpace X] :
    NormedCoordinatePair X (EuclideanSpace ℝ (Fin 1)) where
  coordinates := ContinuousMap.const X 0
  norm := normSeminorm ℝ (EuclideanSpace ℝ (Fin 1))
  definite := fun _ h ↦ norm_eq_zero.mp h

@[simp] theorem zeroCoordinatePair_comap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : (zeroCoordinatePair Y).comap f = zeroCoordinatePair X := rfl

@[simp] theorem zeroCoordinatePair_value {X : Type*} [TopologicalSpace X] (x : X) :
    (zeroCoordinatePair X).norm ((zeroCoordinatePair X).coordinates x) = 0 := by
  change ‖(0 : EuclideanSpace ℝ (Fin 1))‖ = 0
  exact norm_zero

@[simp] theorem zeroCoordinatePair_pseudometric {X : Type*} [TopologicalSpace X] (x y : X) :
    (zeroCoordinatePair X).pseudometric x y = 0 := by
  change ‖(0 : EuclideanSpace ℝ (Fin 1)) - 0‖ = 0
  simp

@[simp] theorem zeroCoordinatePair_unitNormError (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :
    unitNormError (zeroCoordinatePair X).norm (zeroCoordinatePair Y).norm = 0 := by
  simp [unitNormError, zeroCoordinatePair]

@[simp] theorem zeroCoordinatePair_coordinateError {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    (R : Correspondence X Y) :
    coordinateError R (zeroCoordinatePair X).coordinates (zeroCoordinatePair Y).coordinates = 0 := by
  simp [coordinateError, zeroCoordinatePair]

/-- The error of the one-dimensional zero model is exactly the intrinsic diameter. -/
theorem zeroCoordinatePair_metric_error {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X] :
    (⨆ z : X × X, |(zeroCoordinatePair X).pseudometric z.1 z.2 - dist z.1 z.2|) =
      diam (univ : Set X) := by
  simp only [zeroCoordinatePair_pseudometric, zero_sub, abs_neg, abs_of_nonneg dist_nonneg]
  have hb : BddAbove (range (fun z : X × X ↦ dist z.1 z.2)) := (isCompact_range continuous_dist).bddAbove
  apply le_antisymm
  · exact ciSup_le (fun z ↦ dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ z.1) (mem_univ z.2))
  · apply diam_le_of_forall_dist_le (Real.iSup_nonneg (fun _ ↦ dist_nonneg))
    intro x hx y hy
    exact le_ciSup hb (x, y)

/-- Every space of diameter below the tolerance satisfies the zero-model error bound. -/
theorem zeroCoordinatePair_metric_error_lt {X : Type*}
    [MetricSpace X] [CompactSpace X] [Nonempty X] (τ : ℝ)
    (hτ : diam (univ : Set X) < τ) :
    (⨆ z : X × X, |(zeroCoordinatePair X).pseudometric z.1 z.2 - dist z.1 z.2|) < τ := by
  rwa [zeroCoordinatePair_metric_error]

end PaperN.PartII
