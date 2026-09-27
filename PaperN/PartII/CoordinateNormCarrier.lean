import PaperN.PartII.NormedCoordinateClass
import PaperN.Shared.CorrespondenceEmbedding
import Mathlib.Analysis.Normed.Group.Seminorm
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace PaperN.PartII
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A type copy carrying the chosen definite coordinate norm, not the ambient norm. -/
def CoordinateNormCarrier (p : Seminorm ℝ E) (_hp : ∀ v, p v = 0 → v = 0) := E

namespace CoordinateNormCarrier
variable (p : Seminorm ℝ E) (hp : ∀ v, p v = 0 → v = 0)

instance : AddCommGroup (CoordinateNormCarrier p hp) := inferInstanceAs (AddCommGroup E)
instance : Module ℝ (CoordinateNormCarrier p hp) := inferInstanceAs (Module ℝ E)

noncomputable instance : NormedAddCommGroup (CoordinateNormCarrier p hp) :=
  AddGroupNorm.toNormedAddCommGroup {
    toAddGroupSeminorm := p.toAddGroupSeminorm
    eq_zero_of_map_eq_zero' := hp }

noncomputable instance : NormedSpace ℝ (CoordinateNormCarrier p hp) where
  norm_smul_le a v := (map_smul_eq_mul p a v).le

@[simp] theorem norm_eq (v : CoordinateNormCarrier p hp) : ‖v‖ = p v := rfl

/-- The underlying vector spaces are identical; only their norm structures differ. -/
def linearEquiv : E ≃ₗ[ℝ] CoordinateNormCarrier p hp := LinearEquiv.refl ℝ E

instance [FiniteDimensional ℝ E] : FiniteDimensional ℝ (CoordinateNormCarrier p hp) :=
  inferInstanceAs (FiniteDimensional ℝ E)

/-- Every finite-dimensional definite norm induces the original topology. -/
noncomputable def continuousLinearEquiv [FiniteDimensional ℝ E] : E ≃L[ℝ] CoordinateNormCarrier p hp :=
  (linearEquiv p hp).toContinuousLinearEquiv

end CoordinateNormCarrier

/-- The coordinate map as a continuous map into its actual chosen normed space. -/
noncomputable def NormedCoordinatePair.normedCoordinates
    {X : Type*} [TopologicalSpace X] [FiniteDimensional ℝ E]
    (a : NormedCoordinatePair X E) : C(X, CoordinateNormCarrier a.norm a.definite) :=
  ⟨fun x ↦ CoordinateNormCarrier.continuousLinearEquiv a.norm a.definite (a.coordinates x),
    (CoordinateNormCarrier.continuousLinearEquiv a.norm a.definite).continuous.comp a.coordinates.continuous⟩

/-- Distances in the chosen normed carrier are exactly the coordinate pseudometric. -/
theorem NormedCoordinatePair.dist_normedCoordinates
    {X : Type*} [TopologicalSpace X] [FiniteDimensional ℝ E]
    (a : NormedCoordinatePair X E) (x y : X) :
    dist (a.normedCoordinates x) (a.normedCoordinates y) = a.pseudometric x y := by
  rw [dist_eq_norm]
  rfl

namespace NormedCoordinatePair
open Set PaperN.Shared GromovHausdorff
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X] [FiniteDimensional ℝ E]

/-- The compact image in the actual finite-dimensional normed coordinate space. -/
def normedImage (a : NormedCoordinatePair X E) := range a.normedCoordinates

noncomputable instance (a : NormedCoordinatePair X E) : MetricSpace a.normedImage := inferInstanceAs (MetricSpace (range a.normedCoordinates))
instance (a : NormedCoordinatePair X E) : Nonempty a.normedImage := inferInstanceAs (Nonempty (range a.normedCoordinates))
instance (a : NormedCoordinatePair X E) : CompactSpace a.normedImage :=
  isCompact_iff_compactSpace.mp (isCompact_range a.normedCoordinates.continuous)

/-- The separated pseudometric quotient is isometric to the compact coordinate image. -/
theorem quotient_isometry_normedImage (a : NormedCoordinatePair X E) :
    Nonempty (a.pseudometric.Quotient ≃ᵢ a.normedImage) := by
  let R : Correspondence a.pseudometric.Quotient a.normedImage := {
    rel := {z | ∃ x : X, z.1 = a.pseudometric.proj x ∧ z.2.val = a.normedCoordinates x}
    left_total := by
      intro q
      obtain ⟨x, rfl⟩ := a.pseudometric.proj_surjective q
      exact ⟨⟨a.normedCoordinates x, mem_range_self x⟩, x, rfl, rfl⟩
    right_total := by
      rintro ⟨y, x, rfl⟩
      exact ⟨a.pseudometric.proj x, x, rfl, rfl⟩ }
  apply toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp
  apply dist_le_zero.mp
  change ghDist a.pseudometric.Quotient a.normedImage ≤ 0
  have hd : ghDist a.pseudometric.Quotient a.normedImage ≤ (0 : ℝ) / 2 := by
    apply ghDist_le_half_distortion R
    intro u v
    obtain ⟨x, hx, hy⟩ := u.property
    obtain ⟨z, hz, hw⟩ := v.property
    change |dist u.val.1 v.val.1 - dist u.val.2.val v.val.2.val| ≤ 0
    rw [hx, hz, hy, hw, a.pseudometric.dist_proj, a.dist_normedCoordinates]
    simp
  simpa only [zero_div] using hd

end NormedCoordinatePair
end PaperN.PartII
