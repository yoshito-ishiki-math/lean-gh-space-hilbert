import PaperN.PartII.FeatureInvariance
import PaperN.PartII.LocalModel

namespace PaperN.PartII
open PaperN.Shared PaperN.PartI GromovHausdorff
variable {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The normalized dual-sphere feature of an actual local coordinate pair. -/
noncomputable def NormedCoordinatePair.dualFeature (a : NormedCoordinatePair X E) :
    C(X, C(Metric.sphere (0 : E) 1, ℝ)) :=
  ⟨fun x ↦ coordinateDualEmbedding a.norm a.definite (a.coordinates x),
    (coordinateDualLinearIsometry a.norm a.definite).continuous.comp a.normedCoordinates.continuous⟩

/-- The sphere feature realizes the local pseudometric exactly. -/
theorem NormedCoordinatePair.dualFeature_dist (a : NormedCoordinatePair X E) (x y : X) :
    dist (a.dualFeature x) (a.dualFeature y) = a.pseudometric x y := by
  rw [dist_eq_norm]
  change ‖coordinateDualEmbedding a.norm a.definite (a.coordinates x) -
    coordinateDualEmbedding a.norm a.definite (a.coordinates y)‖ = _
  exact coordinateDualEmbedding_norm_sub a.norm a.definite _ _

/-- Its norm is the local coordinate norm, with no loss in constants. -/
theorem NormedCoordinatePair.dualFeature_norm (a : NormedCoordinatePair X E) (x : X) :
    ‖a.dualFeature x‖ = a.norm (a.coordinates x) :=
  coordinateDualEmbedding_norm_eq a.norm a.definite _

/-- Orthogonal equivariance of coordinate pairs gives equivariance of sphere features. -/
theorem NormedCoordinatePair.dualFeature_equivariant
    (a : NormedCoordinatePair X E) (b : NormedCoordinatePair Y E)
    (e : X → Y) (U : E ≃ₗᵢ[ℝ] E)
    (hc : ∀ x, b.coordinates (e x) = U (a.coordinates x))
    (hn : ∀ v, b.norm (U v) = a.norm v) (x : X) :
    b.dualFeature (e x) = orthogonalSphereAction U (a.dualFeature x) := by
  change coordinateDualEmbedding b.norm b.definite (b.coordinates (e x)) = _
  rw [hc]
  exact coordinateDualEmbedding_equivariant a.norm b.norm a.definite b.definite U hn _

/-- The local-model equivariance axiom supplies the required sphere-action witness. -/
theorem LocalModel.dualFeature_equivariance {X₀ : MeasuredCompact.{0}} {τ : ℝ}
    (M : LocalModel X₀ τ) (X Y : MeasuredCompact.{0})
    (hX : toGHSpace X ∈ M.domain) (hY : toGHSpace Y ∈ M.domain) (e : X ≃ᵢ Y)
    (a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin M.dimension)))
    (b : NormedCoordinatePair Y (EuclideanSpace ℝ (Fin M.dimension)))
    (ha : Quotient.mk _ a = M.coordinateClass X hX)
    (hb : Quotient.mk _ b = M.coordinateClass Y hY) :
    ∃ U : EuclideanSpace ℝ (Fin M.dimension) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin M.dimension),
      ∀ x, b.dualFeature (e x) = orthogonalSphereAction U (a.dualFeature x) := by
  obtain ⟨U, hc, hn⟩ := M.equivariance X Y hX hY e a b ha hb
  refine ⟨U, a.dualFeature_equivariant b e U hc ?_⟩
  intro v
  rw [hn, U.symm_apply_apply]

/-- The local model's diameter bound transfers unchanged to the sphere feature. -/
theorem LocalModel.dualFeature_bound {X₀ : MeasuredCompact.{0}} {τ : ℝ}
    (M : LocalModel X₀ τ) (X : MeasuredCompact.{0}) (hX : toGHSpace X ∈ M.domain)
    (a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin M.dimension)))
    (ha : Quotient.mk _ a = M.coordinateClass X hX) (x : X) :
    ‖a.dualFeature x‖ ≤ 2 * Metric.diam (Set.univ : Set X) := by
  rw [a.dualFeature_norm]
  exact M.bound X hX a ha x

end PaperN.PartII
