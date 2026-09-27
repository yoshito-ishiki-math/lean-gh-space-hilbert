import PaperN.PartII.ModelFeatureAssembly

namespace PaperN.PartII
open PaperN.PartI GromovHausdorff
variable {A : ℕ → MeasuredCompact.{0}} {τ : ℕ → ℝ}
    (M : ∀ i, LocalModel (A i) (τ i)) (ρ : PartitionOfUnity ℕ GHSpace)

/-- Actual assembled feature images of isometric carriers determine the same orbit. -/
theorem modelFeatureImage_orbit_eq
    (hρ : ρ.IsSubordinate (fun i ↦ (M i).domain))
    (X Y : MeasuredCompact.{0}) (e : X ≃ᵢ Y) :
    SphereOrbit.projection _ (modelFeatureImage M ρ Y) =
      SphereOrbit.projection _ (modelFeatureImage M ρ X) := by
  classical
  have hq : toGHSpace X = toGHSpace Y :=
    toGHSpace_eq_toGHSpace_iff_isometryEquiv.mpr ⟨e⟩
  have hex : ∀ i, ∃ U : EuclideanSpace ℝ (Fin (M i).dimension) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (M i).dimension),
      i ∈ ρ.finsupport (toGHSpace X) → ∀ x,
        ((M i).chosenPair Y).dualFeature (e x) =
          orthogonalSphereAction U (((M i).chosenPair X).dualFeature x) := by
    intro i
    by_cases hi : i ∈ ρ.finsupport (toGHSpace X)
    · have hX := modelFeature_active_mem M ρ hρ X i hi
      have hY : toGHSpace Y ∈ (M i).domain := hq ▸ hX
      obtain ⟨U, hU⟩ := (M i).dualFeature_equivariance X Y hX hY e _ _
        ((M i).chosenPair_class X hX) ((M i).chosenPair_class Y hY)
      exact ⟨U, fun _ ↦ hU⟩
    · exact ⟨LinearIsometryEquiv.refl ℝ _, fun h ↦ (hi h).elim⟩
  choose U hU using hex
  apply (SphereOrbit.projection_eq_iff _ _ _).mpr
  refine ⟨U, ?_⟩
  unfold modelFeatureImage
  simp only [← hq]
  exact finiteFeatureImage_transport _ _ _ _ _ _ e e.surjective
    (fun i ↦ orthogonalSphereActionEquiv (U i)) hU

/-- The fixed-representative definition agrees with the image of any compact carrier. -/
theorem modelApproximation_eq_image
    (hρ : ρ.IsSubordinate (fun i ↦ (M i).domain)) (X : MeasuredCompact.{0}) :
    modelApproximation M ρ (toGHSpace X) = SphereOrbit.projection _ (modelFeatureImage M ρ X) := by
  obtain ⟨e⟩ := toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp (ghRepresentative_class (toGHSpace X))
  exact (modelFeatureImage_orbit_eq M ρ hρ _ X e).symm

end PaperN.PartII
