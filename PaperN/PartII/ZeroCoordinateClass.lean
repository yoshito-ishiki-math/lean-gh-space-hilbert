import PaperN.PartII.SingletonNeighborhood

namespace PaperN.PartII
open PaperN.Shared PaperN.PartI GromovHausdorff Metric Set Filter
open scoped Topology

/-- The singleton branch assigns this class on every concrete carrier. -/
noncomputable def zeroCoordinateClass (X : Type*) [TopologicalSpace X] :
    NormedCoordinateClass X (EuclideanSpace ℝ (Fin 1)) :=
  Quotient.mk _ (zeroCoordinatePair X)

/-- The zero class is natural even under arbitrary continuous maps. -/
theorem zeroCoordinateClass_comap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : NormedCoordinateClass.comap f (zeroCoordinateClass Y) = zeroCoordinateClass X := rfl

/-- Every representative has zero coordinates and the usual Euclidean norm. -/
theorem zeroCoordinateClass_representative {X : Type*} [TopologicalSpace X]
    (a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin 1)))
    (ha : Quotient.mk _ a = zeroCoordinateClass X) :
    (∀ x, a.coordinates x = 0) ∧ (∀ v, a.norm v = ‖v‖) := by
  obtain ⟨U, hc, hn⟩ := NormedCoordinatePair.equivalent_symm (Quotient.exact ha)
  constructor
  · intro x
    simpa [zeroCoordinatePair] using hc x
  · intro v
    have h := hn (U.symm v)
    simpa [zeroCoordinatePair] using h

/-- Arbitrary representatives admit the required orthogonal change of coordinates. -/
theorem zeroCoordinateClass_equivariance {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin 1)))
    (b : NormedCoordinatePair Y (EuclideanSpace ℝ (Fin 1)))
    (ha : Quotient.mk _ a = zeroCoordinateClass X)
    (hb : Quotient.mk _ b = zeroCoordinateClass Y) :
    ∃ U : EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1),
      (∀ x, b.coordinates (f x) = U (a.coordinates x)) ∧
      (∀ v, b.norm v = a.norm (U.symm v)) := by
  obtain ⟨hac, han⟩ := zeroCoordinateClass_representative a ha
  obtain ⟨hbc, hbn⟩ := zeroCoordinateClass_representative b hb
  exact ⟨LinearIsometryEquiv.refl ℝ _, by simp [hac, hbc], by simp [han, hbn]⟩

/-- All representatives induce the same zero pseudometric. -/
theorem zeroCoordinateClass_pseudometric {X : Type*} [TopologicalSpace X]
    (a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin 1)))
    (ha : Quotient.mk _ a = zeroCoordinateClass X) (x y : X) :
    a.pseudometric x y = 0 := by
  obtain ⟨hc, hn⟩ := zeroCoordinateClass_representative a ha
  change a.norm (a.coordinates x - a.coordinates y) = 0
  simp [hc, hn]

/-- The diameter bound holds for every representative, not merely the chosen pair. -/
theorem zeroCoordinateClass_bound {X : Type*} [MetricSpace X]
    (a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin 1)))
    (ha : Quotient.mk _ a = zeroCoordinateClass X) (x : X) :
    a.norm (a.coordinates x) ≤ 2 * diam (univ : Set X) := by
  obtain ⟨hc, hn⟩ := zeroCoordinateClass_representative a ha
  simp only [hc, hn, norm_zero]
  positivity

/-- The continuous GH error formula holds for every coordinate representative. -/
theorem zeroCoordinateClass_metric_error (X : MeasuredCompact.{0})
    (a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin 1)))
    (ha : Quotient.mk _ a = zeroCoordinateClass X) :
    (⨆ z : X × X, |a.pseudometric z.1 z.2 - dist z.1 z.2|) =
      ghDiameter (toGHSpace X) := by
  rw [← zeroCoordinatePair_metric_error_eq_ghDiameter X]
  simp only [zeroCoordinateClass_pseudometric a ha, zeroCoordinatePair_pseudometric]

/-- Representatives may be fixed before choosing any correspondences. -/
theorem zeroCoordinateClass_representatives_converge
    (Xs : ℕ → MeasuredCompact.{0}) (X : MeasuredCompact.{0}) :
    ∃ a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin 1)),
      ∃ as : ∀ k, NormedCoordinatePair (Xs k) (EuclideanSpace ℝ (Fin 1)),
        Quotient.mk _ a = zeroCoordinateClass X ∧
        (∀ k, Quotient.mk _ (as k) = zeroCoordinateClass (Xs k)) ∧
        Tendsto (fun k ↦ unitNormError (as k).norm a.norm) atTop (𝓝 0) ∧
        ∀ R : ∀ k, Correspondence (Xs k) X,
          Tendsto (fun k ↦ coordinateError (R k) (as k).coordinates a.coordinates) atTop (𝓝 0) := by
  refine ⟨zeroCoordinatePair X, fun k ↦ zeroCoordinatePair (Xs k), rfl, fun _ ↦ rfl, ?_, ?_⟩
  · simpa only [zeroCoordinatePair_unitNormError] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
  · intro R
    simpa only [zeroCoordinatePair_coordinateError] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))

end PaperN.PartII
