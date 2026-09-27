import PaperN.PartII.ModelFeatureInvariance

namespace PaperN.PartII
open PaperN.PartI GromovHausdorff

/-- Enlarging the finite index set by zero-weight blocks leaves the compact image unchanged. -/
theorem finiteFeatureImage_eq_of_subset {I X : Type*} [DecidableEq I]
    [TopologicalSpace X] [CompactSpace X] [Nonempty X] {B : I → Type*}
    [∀ i, NormedAddCommGroup (B i)] [∀ i, NormedSpace ℝ (B i)]
    (s t : Finset I) (hst : s ⊆ t) (w : I → ℝ) (f : ∀ i, X → B i)
    (hs : ∀ i ∈ s, Continuous (f i)) (ht : ∀ i ∈ t, Continuous (f i))
    (hw : ∀ i ∈ t, i ∉ s → w i = 0) :
    finiteFeatureImage s w f hs = finiteFeatureImage t w f ht := by
  apply SetLike.coe_injective
  change Set.range (fun x ↦ finiteBlockFeature s w (fun i ↦ f i x)) =
    Set.range (fun x ↦ finiteBlockFeature t w (fun i ↦ f i x))
  congr 1
  funext x
  exact finiteBlockFeature_eq_of_subset s t hst w _ hw

variable {A : ℕ → MeasuredCompact.{0}} {τ : ℕ → ℝ}
    (M : ∀ i, LocalModel (A i) (τ i)) (ρ : PartitionOfUnity ℕ GHSpace)

/-- Arbitrary local coordinate representatives on the active set give the same global orbit. -/
theorem modelApproximation_eq_representatives
    (hρ : ρ.IsSubordinate (fun i ↦ (M i).domain)) (X : MeasuredCompact.{0})
    (a : ∀ i, NormedCoordinatePair X (EuclideanSpace ℝ (Fin (M i).dimension)))
    (ha : ∀ i (hi : i ∈ ρ.finsupport (toGHSpace X)),
      Quotient.mk _ (a i) = (M i).coordinateClass X (modelFeature_active_mem M ρ hρ X i hi)) :
    modelApproximation M ρ (toGHSpace X) = SphereOrbit.projection _
      (finiteFeatureImage (ρ.finsupport (toGHSpace X)) (fun i ↦ ρ i (toGHSpace X))
        (fun i ↦ (a i).dualFeature) (fun i _ ↦ (a i).dualFeature.continuous)) := by
  classical
  rw [modelApproximation_eq_image M ρ hρ X]
  symm
  have hex : ∀ i, ∃ U : EuclideanSpace ℝ (Fin (M i).dimension) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (M i).dimension),
      i ∈ ρ.finsupport (toGHSpace X) → ∀ x,
        (a i).dualFeature x = orthogonalSphereAction U (((M i).chosenPair X).dualFeature x) := by
    intro i
    by_cases hi : i ∈ ρ.finsupport (toGHSpace X)
    · have hX := modelFeature_active_mem M ρ hρ X i hi
      obtain ⟨U, hU⟩ := (M i).dualFeature_equivariance X X hX hX (IsometryEquiv.refl X)
        _ (a i) ((M i).chosenPair_class X hX) (ha i hi)
      exact ⟨U, fun _ ↦ hU⟩
    · exact ⟨LinearIsometryEquiv.refl ℝ _, fun h ↦ (hi h).elim⟩
  choose U hU using hex
  apply (SphereOrbit.projection_eq_iff _ _ _).mpr
  refine ⟨U, ?_⟩
  exact finiteFeatureImage_transport _ _ _ _ _ _ id Function.surjective_id
    (fun i ↦ orthogonalSphereActionEquiv (U i)) hU

/-- The global orbit may be computed on any common finite superset of the active indices. -/
theorem modelApproximation_eq_representatives_on_superset
    (hρ : ρ.IsSubordinate (fun i ↦ (M i).domain)) (X : MeasuredCompact.{0})
    (J : Finset ℕ) (hJ : ρ.finsupport (toGHSpace X) ⊆ J)
    (a : ∀ i, NormedCoordinatePair X (EuclideanSpace ℝ (Fin (M i).dimension)))
    (ha : ∀ i (hi : i ∈ ρ.finsupport (toGHSpace X)),
      Quotient.mk _ (a i) = (M i).coordinateClass X (modelFeature_active_mem M ρ hρ X i hi)) :
    modelApproximation M ρ (toGHSpace X) = SphereOrbit.projection _
      (finiteFeatureImage J (fun i ↦ ρ i (toGHSpace X))
        (fun i ↦ (a i).dualFeature) (fun i _ ↦ (a i).dualFeature.continuous)) := by
  rw [modelApproximation_eq_representatives M ρ hρ X a ha]
  congr 1
  apply finiteFeatureImage_eq_of_subset _ J hJ
  intro i _ hi
  simpa only [ρ.mem_finsupport, Function.mem_support, not_not] using hi

end PaperN.PartII
