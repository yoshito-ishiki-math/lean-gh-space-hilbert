import PaperN.PartII.LocalDualFeature
import PaperN.PartII.LocalModelPartition
import PaperN.PartII.LocalModelGHMap

namespace PaperN.PartII
open PaperN.Shared PaperN.PartI GromovHausdorff TopologicalSpace

/-- Choose an actual coordinate pair on the model domain, with a zero fallback elsewhere. -/
noncomputable def LocalModel.chosenPair {X₀ : MeasuredCompact.{0}} {τ : ℝ}
    (M : LocalModel X₀ τ) (X : MeasuredCompact.{0}) :
    NormedCoordinatePair X (EuclideanSpace ℝ (Fin M.dimension)) := by
  classical
  exact if h : toGHSpace X ∈ M.domain then (M.coordinateClass X h).out else
    { coordinates := 0, norm := normSeminorm ℝ _, definite := fun v hv ↦ norm_eq_zero.mp hv }

/-- On the domain the chosen pair represents the prescribed class. -/
theorem LocalModel.chosenPair_class {X₀ : MeasuredCompact.{0}} {τ : ℝ}
    (M : LocalModel X₀ τ) (X : MeasuredCompact.{0}) (hX : toGHSpace X ∈ M.domain) :
    Quotient.mk _ (M.chosenPair X) = M.coordinateClass X hX := by
  classical
  simp only [LocalModel.chosenPair, dif_pos hX]
  exact Quotient.out_eq _

variable {A : ℕ → MeasuredCompact.{0}} {τ : ℕ → ℝ}
    (M : ∀ i, LocalModel (A i) (τ i)) (ρ : PartitionOfUnity ℕ GHSpace)

/-- The compact image obtained by assembling exactly the active partition blocks. -/
noncomputable def modelFeatureImage (X : MeasuredCompact.{0}) :
    NonemptyCompacts (SphereBlockSum (fun i ↦ (M i).dimension)) :=
  finiteFeatureImage (ρ.finsupport (toGHSpace X)) (fun i ↦ ρ i (toGHSpace X))
    (fun i ↦ (M i).chosenPair X |>.dualFeature) (fun i _ ↦ ((M i).chosenPair X).dualFeature.continuous)

/-- Active partition indices lie in the corresponding local-model domains. -/
theorem modelFeature_active_mem (hρ : ρ.IsSubordinate (fun i ↦ (M i).domain))
    (X : MeasuredCompact.{0}) (i : ℕ) (hi : i ∈ ρ.finsupport (toGHSpace X)) :
    toGHSpace X ∈ (M i).domain := by
  apply hρ i
  apply subset_closure
  exact (ρ.mem_finsupport _).mp hi

/-- The assembled point map retains the uniform twice-diameter bound. -/
theorem modelFeature_norm_le (hρ : ρ.IsSubordinate (fun i ↦ (M i).domain))
    (X : MeasuredCompact.{0}) (x : X) :
    ‖finiteBlockFeature (ρ.finsupport (toGHSpace X)) (fun i ↦ ρ i (toGHSpace X))
      (fun i ↦ ((M i).chosenPair X).dualFeature x)‖ ≤ 2 * Metric.diam (Set.univ : Set X) := by
  rw [finiteBlockFeature_norm _ _ (fun i _ ↦ ρ.nonneg i _)]
  calc
    _ ≤ ∑ i ∈ ρ.finsupport (toGHSpace X), ρ i (toGHSpace X) * (2 * Metric.diam (Set.univ : Set X)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        ((M i).dualFeature_bound X (modelFeature_active_mem M ρ hρ X i hi) _
          ((M i).chosenPair_class X (modelFeature_active_mem M ρ hρ X i hi)) x) (ρ.nonneg i _)
    _ = _ := by rw [← Finset.sum_mul, ρ.sum_finsupport (Set.mem_univ _), one_mul]

/-- The actual assembled image approximates its original compact carrier. -/
theorem modelFeatureImage_ghDist_lt (hρ : ρ.IsSubordinate (fun i ↦ (M i).domain))
    (X : MeasuredCompact.{0}) (ε : ℝ)
    (he : ∀ i, toGHSpace X ∈ (M i).domain → (M i).error (toGHSpace X) < ε) :
    dist (toGHSpace X) (modelFeatureImage M ρ X).toGHSpace < ε / 2 := by
  rw [← ofMetric_gh X]
  apply finiteFeatureImage_ghDist_lt _ _ (fun i _ ↦ ρ.nonneg i _)
    (ρ.sum_finsupport (Set.mem_univ _)) _ _
    (fun i ↦ ((M i).chosenPair X).pseudometric)
    (fun i _ x y ↦ ((M i).chosenPair X).dualFeature_dist x y)
  intro i hi _
  have hX := modelFeature_active_mem M ρ hρ X i hi
  have herr := (M i).error_eq X hX ((M i).chosenPair X) ((M i).chosenPair_class X hX)
  rw [uniform_metric_error_eq_norm] at herr
  rw [norm_sub_rev, ← herr]
  exact he i hX

/-- The global candidate map, using the fixed representative of each GH class. -/
noncomputable def modelApproximation (q : GHSpace) :
    SphereOrbit.Space (fun i ↦ (M i).dimension) :=
  SphereOrbit.projection _ (modelFeatureImage M ρ (ghRepresentative q))

/-- Realization of the global candidate has the prescribed pointwise accuracy. -/
theorem modelApproximation_realization_dist_lt
    (hρ : ρ.IsSubordinate (fun i ↦ (M i).domain)) (ε : GHSpace → ℝ)
    (he : ∀ i q, q ∈ (M i).domain → (M i).error q < ε q) (q : GHSpace) :
    dist q (SphereOrbit.realization _ (modelApproximation M ρ q)) < ε q / 2 := by
  have h := modelFeatureImage_ghDist_lt M ρ hρ (ghRepresentative q) (ε q)
    (fun i hi ↦ by simpa only [ghRepresentative_class] using he i _ hi)
  simpa only [modelApproximation, SphereOrbit.realization_projection,
    ghRepresentative_class] using h

end PaperN.PartII
