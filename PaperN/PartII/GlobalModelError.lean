import PaperN.PartII.GlobalOrbitApproximation

namespace PaperN.PartII
open PaperN.Shared PaperN.PartI GromovHausdorff

/-- Uniform metric error is unchanged by a carrier isometry respecting the pseudometric. -/
theorem uniform_metric_error_isometry {X Y : Type*}
    [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
    (e : X ≃ᵢ Y) (d : ContinuousPseudometric X) (c : ContinuousPseudometric Y)
    (h : ∀ x y, c (e x) (e y) = d x y) :
    ‖(ContinuousPseudometric.ofMetric X).kernel - d.kernel‖ =
      ‖(ContinuousPseudometric.ofMetric Y).kernel - c.kernel‖ := by
  simp only [ContinuousMap.norm_eq_iSup_norm]
  rw [← (Equiv.prodCongr e.toEquiv e.toEquiv).iSup_comp]
  congr 1
  funext z
  change ‖dist z.1 z.2 - d z.1 z.2‖ = ‖dist (e z.1) (e z.2) - c (e z.1) (e z.2)‖
  rw [e.dist_eq, h]

variable {A : ℕ → MeasuredCompact.{0}} {τ : ℕ → ℝ}
    (M : ∀ i, LocalModel (A i) (τ i)) (ρ : PartitionOfUnity ℕ GHSpace)

/-- The global pseudometric on a concrete carrier. -/
noncomputable def modelPseudometric (X : MeasuredCompact.{0}) : ContinuousPseudometric X :=
  weightedPseudometric (ρ.finsupport (toGHSpace X)) (fun i ↦ ρ i (toGHSpace X))
    (fun i _ ↦ ρ.nonneg i _) (fun i ↦ ((M i).chosenPair X).pseudometric)

/-- The global pseudometric is natural under isometries of input carriers. -/
theorem modelPseudometric_equivariant
    (hρ : ρ.IsSubordinate (fun i ↦ (M i).domain))
    (X Y : MeasuredCompact.{0}) (e : X ≃ᵢ Y) (x y : X) :
    modelPseudometric M ρ Y (e x) (e y) = modelPseudometric M ρ X x y := by
  have hq : toGHSpace X = toGHSpace Y :=
    toGHSpace_eq_toGHSpace_iff_isometryEquiv.mpr ⟨e⟩
  simp only [modelPseudometric, weightedPseudometric_apply, ← hq]
  apply Finset.sum_congr rfl
  intro i hi
  have hX := modelFeature_active_mem M ρ hρ X i hi
  have hY : toGHSpace Y ∈ (M i).domain := hq ▸ hX
  exact congrArg (ρ i (toGHSpace X) * ·)
    ((M i).pseudometric_invariant X Y hX hY e _ _
      ((M i).chosenPair_class X hX) ((M i).chosenPair_class Y hY) x y)

/-- The manuscript's uniform pseudometric error on a concrete carrier. -/
noncomputable def modelUniformError (X : MeasuredCompact.{0}) : ℝ :=
  ‖(ContinuousPseudometric.ofMetric X).kernel - (modelPseudometric M ρ X).kernel‖

/-- Uniform pseudometric error is independent of the input representative. -/
theorem modelUniformError_invariant
    (hρ : ρ.IsSubordinate (fun i ↦ (M i).domain))
    (X Y : MeasuredCompact.{0}) (e : X ≃ᵢ Y) :
    modelUniformError M ρ X = modelUniformError M ρ Y :=
  uniform_metric_error_isometry e _ _ (modelPseudometric_equivariant M ρ hρ X Y e)

/-- Uniform pseudometric error as a function on GH space. -/
noncomputable def modelError (q : GHSpace) : ℝ :=
  modelUniformError M ρ (ghRepresentative q)

/-- The GH-level error can be calculated on any compact representative. -/
theorem modelError_eq (hρ : ρ.IsSubordinate (fun i ↦ (M i).domain))
    (X : MeasuredCompact.{0}) : modelError M ρ (toGHSpace X) = modelUniformError M ρ X := by
  obtain ⟨e⟩ := toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp (ghRepresentative_class (toGHSpace X))
  exact modelUniformError_invariant M ρ hρ _ X e

/-- The uniform error, not only GH distance, satisfies the prescribed strict bound. -/
theorem modelError_lt (hρ : ρ.IsSubordinate (fun i ↦ (M i).domain))
    (ε : GHSpace → ℝ) (he : ∀ i q, q ∈ (M i).domain → (M i).error q < ε q)
    (q : GHSpace) : modelError M ρ q < ε q := by
  let X := ghRepresentative q
  apply weightedPseudometric_error_lt _ _ (fun i _ ↦ ρ.nonneg i _)
    (ρ.sum_finsupport (Set.mem_univ (toGHSpace X)))
  intro i hi _
  have hX := modelFeature_active_mem M ρ hρ X i hi
  have herr := (M i).error_eq X hX ((M i).chosenPair X) ((M i).chosenPair_class X hX)
  rw [uniform_metric_error_eq_norm] at herr
  rw [norm_sub_rev, ← herr]
  simpa only [X, ghRepresentative_class] using he i _ hX

/-- The global pseudometric quotient is the actual assembled feature image. -/
theorem modelFeatureImage_gh_eq (X : MeasuredCompact.{0}) :
    (modelFeatureImage M ρ X).toGHSpace = (modelPseudometric M ρ X).gh :=
  finiteFeatureImage_gh_eq _ _ (fun i _ ↦ ρ.nonneg i _) _ _ _
    (fun i _ x y ↦ ((M i).chosenPair X).dualFeature_dist x y)

theorem modelError_nonneg (q : GHSpace) : 0 ≤ modelError M ρ q := norm_nonneg _

/-- Realization is within half the actual uniform pseudometric error. -/
theorem modelApproximation_dist_le_error (q : GHSpace) :
    dist q (SphereOrbit.realization _ (modelApproximation M ρ q)) ≤ modelError M ρ q / 2 := by
  have h := quotient_ghDist_le_norm (ContinuousPseudometric.ofMetric (ghRepresentative q))
    (modelPseudometric M ρ (ghRepresentative q))
  change dist (ContinuousPseudometric.ofMetric (ghRepresentative q)).gh
    (modelPseudometric M ρ (ghRepresentative q)).gh ≤ _ at h
  rw [ofMetric_gh, ghRepresentative_class] at h
  simpa only [modelApproximation, SphereOrbit.realization_projection, modelFeatureImage_gh_eq,
    modelError, modelUniformError] using h

end PaperN.PartII
