import PaperN.PartII.MetricApproximationError

namespace PaperN.PartII
open PaperN.Shared Filter
open scoped Topology

/-- A correspondence controls all source coordinates by its coordinate error
and the bound for the target coordinates. -/
theorem coordinateBound_le_error_add
    {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    [NormedAddCommGroup E] (R : Correspondence X Y) (f : C(X, E)) (g : C(Y, E)) :
    coordinateBound f ≤ coordinateError R f g + coordinateBound g := by
  have he : BddAbove (Set.range (fun z : R.rel ↦ ‖f z.val.1 - g z.val.2‖)) := by
    apply (isCompact_range
      ((f.continuous.comp continuous_fst).sub (g.continuous.comp continuous_snd)).norm).bddAbove.mono
    rintro _ ⟨z, rfl⟩
    exact ⟨z.val, rfl⟩
  have hg := (isCompact_range g.continuous.norm).bddAbove
  apply ciSup_le
  intro x
  obtain ⟨y, hy⟩ := R.left_total x
  calc
    ‖f x‖ ≤ ‖f x - g y‖ + ‖g y‖ := norm_le_norm_sub_add _ _
    _ ≤ coordinateError R f g + coordinateBound g :=
      add_le_add (le_ciSup he ⟨(x, y), hy⟩) (le_ciSup hg y)

/-- Vanishing coordinate error supplies the eventual Euclidean bound automatically. -/
theorem coordinateBound_eventually_le_of_error_tendsto
    {X E : Type*} (Xs : ℕ → Type*) [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    [∀ k, TopologicalSpace (Xs k)] [∀ k, CompactSpace (Xs k)] [∀ k, Nonempty (Xs k)]
    [NormedAddCommGroup E] (R : ∀ k, Correspondence (Xs k) X)
    (fs : ∀ k, C(Xs k, E)) (f : C(X, E))
    (hc : Tendsto (fun k ↦ coordinateError (R k) (fs k) f) atTop (𝓝 0)) :
    ∀ᶠ k in atTop, coordinateBound (fs k) ≤ 1 + coordinateBound f := by
  filter_upwards [hc.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with k hk
  exact (coordinateBound_le_error_add (R k) (fs k) f).trans (add_le_add hk.le le_rfl)

/-- Norm and coordinate convergence suffice; no extra coordinate bound is assumed. -/
theorem coordinate_metric_error_tendsto_of_errors
    {X : Type*} (Xs : ℕ → Type*) [MetricSpace X] [CompactSpace X] [Nonempty X]
    [∀ k, MetricSpace (Xs k)] [∀ k, CompactSpace (Xs k)] [∀ k, Nonempty (Xs k)]
    (n : ℕ) [NeZero n] (R : ∀ k, Correspondence (Xs k) X)
    (as : ∀ k, NormedCoordinatePair (Xs k) (EuclideanSpace ℝ (Fin n)))
    (a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin n)))
    (hn : Tendsto (fun k ↦ unitNormError (as k).norm a.norm) atTop (𝓝 0))
    (hc : Tendsto (fun k ↦ coordinateError (R k) (as k).coordinates a.coordinates) atTop (𝓝 0))
    (hd : Tendsto (fun k ↦ (R k).distortion) atTop (𝓝 0)) :
    Tendsto (fun k ↦ ⨆ z : Xs k × Xs k,
      |(as k).pseudometric z.1 z.2 - dist z.1 z.2|) atTop
      (𝓝 (⨆ z : X × X, |a.pseudometric z.1 z.2 - dist z.1 z.2|)) := by
  exact coordinate_metric_error_tendsto Xs n R as a (1 + coordinateBound a.coordinates)
    (coordinateBound_eventually_le_of_error_tendsto Xs R (fun k ↦ (as k).coordinates)
      a.coordinates hc) hn hc hd

end PaperN.PartII
