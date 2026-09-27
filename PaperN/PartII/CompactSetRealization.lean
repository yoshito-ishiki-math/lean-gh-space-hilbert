import PaperN.PartII.SphereOrbitSpace

namespace PaperN.PartII
open TopologicalSpace GromovHausdorff

/-- Passing a compact subset through an ambient isometry preserves its GH class. -/
theorem compactSetIsometry_toGHSpace {E : Type*} [MetricSpace E]
    (U : E ≃ᵢ E) (K : NonemptyCompacts E) :
    (compactSetIsometry U K).toGHSpace = K.toGHSpace := by
  let f : K → compactSetIsometry U K := fun x ↦ ⟨U x.val, Set.mem_image_of_mem U x.property⟩
  have hi : Isometry f := fun x y ↦ U.isometry x.val y.val
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact (toGHSpace_eq_toGHSpace_iff_isometryEquiv.mpr
    ⟨{ toEquiv := Equiv.ofBijective f ⟨hi.injective, hs⟩, isometry_toFun := hi }⟩).symm

namespace SphereOrbit
variable (n : ℕ → ℕ)
noncomputable local instance : ∀ i, TopologicalSpace (EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ]
    EuclideanSpace ℝ (Fin (n i))) := fun _ ↦ orthogonalOperatorTopology
local instance : CompactSpace (GroupType n) := orthogonalProduct_compactSpace n
noncomputable local instance : MulAction (GroupType n) (NonemptyCompacts (SphereBlockSum n)) := sphereCompactMulAction n
local instance : ContinuousSMul (GroupType n) (NonemptyCompacts (SphereBlockSum n)) := continuousSMul n
local instance : IsIsometricSMul (GroupType n) (NonemptyCompacts (SphereBlockSum n)) := isIsometricSMul n

/-- The realization map from the concrete orbit space to GH space. -/
noncomputable def realization : Space n → GHSpace :=
  Quotient.lift (fun K : NonemptyCompacts (SphereBlockSum n) ↦ K.toGHSpace) (by
    intro K L h
    obtain ⟨U, rfl⟩ := (compactOrbitDist_eq_zero_iff K L).mp h
    exact compactSetIsometry_toGHSpace (sphereBlockSumAction n U).toIsometryEquiv L)

@[simp] theorem realization_projection (K : NonemptyCompacts (SphereBlockSum n)) :
    realization n (projection n K) = K.toGHSpace := rfl

/-- Realization is 1-Lipschitz for the orbit metric. -/
theorem realization_lipschitz : LipschitzWith 1 (realization n) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro K L
  obtain ⟨U, hU⟩ := compactOrbitDist_attained (G := GroupType n) K L
  change dist K.toGHSpace L.toGHSpace ≤ (1 : ℝ) * compactOrbitDist (G := GroupType n) K L
  rw [one_mul, hU]
  have h := ghDist_le_nonemptyCompacts_dist K (compactSetIsometry (sphereBlockSumAction n U).toIsometryEquiv L)
  rwa [compactSetIsometry_toGHSpace] at h

end SphereOrbit
end PaperN.PartII
