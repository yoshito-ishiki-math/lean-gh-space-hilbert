import PaperN.PartII.BestApproximationContinuity

namespace PaperN.PartII
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- An isometric transport of a subspace transports its best approximation. -/
theorem bestApproximation_isometry [StrictConvexSpace ℝ G]
    (S : Submodule ℝ F) (T : Submodule ℝ G)
    [FiniteDimensional ℝ S] [FiniteDimensional ℝ T]
    (U : F →ₗᵢ[ℝ] G) (hST : ∀ y, y ∈ T ↔ ∃ x ∈ S, U x = y) (x : F) :
    (bestApproximation T (U x) : G) = U (bestApproximation S x) := by
  have hm : U (bestApproximation S x) ∈ T :=
    (hST _).mpr ⟨_, (bestApproximation S x).property, rfl⟩
  have h := bestApproximation_unique T (U x)
    (bestApproximation T (U x)) ⟨U (bestApproximation S x), hm⟩
    (bestApproximation_spec T (U x)) (by
      intro b
      obtain ⟨c, hc, hcb⟩ := (hST b).mp b.property
      have hi := bestApproximation_spec S x ⟨c, hc⟩
      change ‖U x - U (bestApproximation S x)‖ ≤ ‖U x - (b : G)‖
      rw [← hcb, ← U.map_sub, ← U.map_sub, U.norm_map, U.norm_map]
      exact hi)
  exact congrArg Subtype.val h

end PaperN.PartII

namespace PaperN.PartII
open MeasureTheory
variable {X ι : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Fintype ι]
  (μ : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
  (p : ENNReal) [Fact (1 ≤ p)] [StrictConvexSpace ℝ (Lp ℝ p μ)]

theorem coordinateLpMinimizer_change_basis (v w : ι → C(X, ℝ))
    (hw : LinearIndependent ℝ w) (O : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (hO : ∀ a, coordinateLpMap μ p w (O a) = coordinateLpMap μ p v a)
    (f : Lp ℝ p μ) :
    coordinateLpMinimizer μ p w f = O (coordinateLpMinimizer μ p v f) := by
  apply coordinateLp_minimizer_unique μ p w hw f
  · exact coordinateLpMinimizer_spec μ p w f
  · intro c
    rw [hO]
    have h := coordinateLpMinimizer_spec μ p v f (O.symm c)
    simpa only [← hO, O.apply_symm_apply] using h

omit [μ.IsOpenPosMeasure] [StrictConvexSpace ℝ (Lp ℝ p μ)] in
theorem coordinateLpNorm_change_basis (v w : ι → C(X, ℝ))
    (O : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (hO : ∀ a, coordinateLpMap μ p w (O a) = coordinateLpMap μ p v a)
    (a : EuclideanSpace ℝ ι) : coordinateLpNorm μ p w (O a) = coordinateLpNorm μ p v a := by
  change ‖coordinateLpMap μ p w (O a)‖ = ‖coordinateLpMap μ p v a‖
  rw [hO]

end PaperN.PartII

namespace PaperN.PartII
open MeasureTheory
variable {X ι : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Fintype ι]
  (μ : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
  (p : ENNReal) [Fact (1 ≤ p)] [StrictConvexSpace ℝ (Lp ℝ p μ)]

noncomputable def bestApproximationCoordinatePair (v : ι → C(X, ℝ))
    (hv : LinearIndependent ℝ v) : NormedCoordinatePair X (EuclideanSpace ℝ ι) :=
  coordinateLpPair μ p v hv (bestApproximationCoordinates μ p v hv)

theorem bestApproximationCoordinatePair_equivalent (v w : ι → C(X, ℝ))
    (hv : LinearIndependent ℝ v) (hw : LinearIndependent ℝ w)
    (O : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (hO : ∀ a, coordinateLpMap μ p w (O a) = coordinateLpMap μ p v a) :
    NormedCoordinatePair.Equivalent (bestApproximationCoordinatePair μ p v hv)
      (bestApproximationCoordinatePair μ p w hw) := by
  refine ⟨O, ?_, ?_⟩
  · intro x
    exact coordinateLpMinimizer_change_basis μ p v w hw O hO
      (ContinuousMap.toLp p μ ℝ (distanceProfile x))
  · exact coordinateLpNorm_change_basis μ p v w O hO

theorem bestApproximationCoordinatePair_class_eq (v w : ι → C(X, ℝ))
    (hv : LinearIndependent ℝ v) (hw : LinearIndependent ℝ w)
    (O : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (hO : ∀ a, coordinateLpMap μ p w (O a) = coordinateLpMap μ p v a) :
    (Quotient.mk _ (bestApproximationCoordinatePair μ p v hv) :
      NormedCoordinateClass X (EuclideanSpace ℝ ι)) =
      Quotient.mk _ (bestApproximationCoordinatePair μ p w hw) :=
  Quotient.sound (bestApproximationCoordinatePair_equivalent μ p v w hv hw O hO)

end PaperN.PartII
