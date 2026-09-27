import PaperN.PartII.FeatureImage

namespace PaperN.PartII
open TopologicalSpace Set
variable {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y] [MetricSpace E]

/-- Surjective change of carrier and equivariance transport the entire compact image. -/
theorem featureImage_transport (f : X → E) (g : Y → E)
    (hf : Continuous f) (hg : Continuous g) (e : X → Y) (he : Function.Surjective e)
    (U : E ≃ᵢ E) (h : ∀ x, g (e x) = U (f x)) :
    featureImage g hg = compactSetIsometry U (featureImage f hf) := by
  apply SetLike.coe_injective
  change range g = U '' range f
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := he y
    exact ⟨f x, mem_range_self x, (h x).symm⟩
  · rintro ⟨v, ⟨x, rfl⟩, rfl⟩
    exact ⟨e x, h x⟩

variable {I : Type*} [DecidableEq I] {B : I → Type*}
    [∀ i, NormedAddCommGroup (B i)] [∀ i, NormedSpace ℝ (B i)]

/-- Blockwise equivariance on selected indices transports the finite feature image. -/
theorem finiteFeatureImage_transport (s : Finset I) (w : I → ℝ)
    (f : ∀ i, X → B i) (g : ∀ i, Y → B i)
    (hf : ∀ i ∈ s, Continuous (f i)) (hg : ∀ i ∈ s, Continuous (g i))
    (e : X → Y) (he : Function.Surjective e) (U : ∀ i, B i ≃ₗᵢ[ℝ] B i)
    (h : ∀ i ∈ s, ∀ x, g i (e x) = U i (f i x)) :
    finiteFeatureImage s w g hg =
      compactSetIsometry (blockSumActionEquiv U).toIsometryEquiv (finiteFeatureImage s w f hf) := by
  apply featureImage_transport _ _ _ _ e he
  intro x
  change finiteBlockFeature s w (fun i ↦ g i (e x)) =
    blockSumAction U (finiteBlockFeature s w (fun i ↦ f i x))
  rw [finiteBlockFeature_equivariant]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  rw [h i hi x]

/-- Sphere-feature images related by an orthogonal action give the same orbit point. -/
theorem sphereFeatureImage_orbit_eq (n : ℕ → ℕ)
    (f : X → SphereBlockSum n) (g : Y → SphereBlockSum n)
    (hf : Continuous f) (hg : Continuous g) (e : X → Y) (he : Function.Surjective e)
    (U : SphereOrbit.GroupType n) (h : ∀ x, g (e x) = sphereBlockSumAction n U (f x)) :
    SphereOrbit.projection n (featureImage g hg) = SphereOrbit.projection n (featureImage f hf) := by
  apply (SphereOrbit.projection_eq_iff n _ _).mpr
  exact ⟨U, featureImage_transport f g hf hg e he (sphereBlockSumAction n U).toIsometryEquiv h⟩

end PaperN.PartII
