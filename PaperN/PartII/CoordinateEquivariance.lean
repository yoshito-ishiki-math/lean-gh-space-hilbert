import PaperN.PartII.CoordinatePullback
import PaperN.PartII.SpectralCutoffEquiv
import PaperN.PartII.LocalSpectralContinuity

namespace PaperN.PartII

/-- Equality of pulled-back classes supplies the manuscript's orthogonal witness
for any pair of representatives. -/
theorem coordinate_equivariance_of_comap_eq
    {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : C(X, Y))
    (A : NormedCoordinateClass X E) (B : NormedCoordinateClass Y E)
    (h : B.comap f = A) (a : NormedCoordinatePair X E) (b : NormedCoordinatePair Y E)
    (ha : Quotient.mk _ a = A) (hb : Quotient.mk _ b = B) :
    ∃ U : E ≃ₗᵢ[ℝ] E, (∀ x, b.coordinates (f x) = U (a.coordinates x)) ∧
      ∀ v, b.norm v = a.norm (U.symm v) := by
  have heq : (Quotient.mk _ a : NormedCoordinateClass X E) = Quotient.mk _ (b.comap f) := by
    rw [ha, ← NormedCoordinateClass.comap_mk, hb, h]
  obtain ⟨U, hc, hn⟩ := Quotient.exact heq
  refine ⟨U, hc, fun v ↦ ?_⟩
  simpa only [NormedCoordinatePair.comap, U.apply_symm_apply] using hn (U.symm v)

/-- Class naturality also transports the intrinsic approximation error. -/
theorem coordinate_metric_error_eq_of_comap_eq
    {X Y E : Type*} [MetricSpace X] [MetricSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : X ≃ᵢ Y) (A : NormedCoordinateClass X E) (B : NormedCoordinateClass Y E)
    (h : B.comap ⟨e, e.continuous⟩ = A) :
    (⨆ z : X × X, |(NormedCoordinateClass.pseudometric X E A) z.1 z.2 - dist z.1 z.2|) =
      (⨆ z : Y × Y, |(NormedCoordinateClass.pseudometric Y E B) z.1 z.2 - dist z.1 z.2|) := by
  apply (e.toEquiv.prodCongr e.toEquiv).iSup_congr
  intro z
  change |(NormedCoordinateClass.pseudometric Y E B) (e z.1) (e z.2) - dist (e z.1) (e z.2)| =
    |(NormedCoordinateClass.pseudometric X E A) z.1 z.2 - dist z.1 z.2|
  have hp := NormedCoordinateClass.pseudometric_comap_apply (E := E) ⟨e, e.continuous⟩ B z.1 z.2
  rw [h] at hp
  rw [hp, e.dist_eq]
  rfl

namespace AmbientKernel.SpectralModelNeighborhood
open MeasureTheory PaperN.PartI GromovHausdorff
variable {hm : GHPMetricInput.{0}} {hs : InvariantFiberLawSelectionStatement hm}
  {X₀ : MeasuredCompact.{0}} {η : ℝ} {n : ℕ}

/-- Whole-carrier naturality of the actual classes in the spectral neighborhood. -/
theorem coordinateClass_comap (B : SpectralModelNeighborhood hm hs X₀ η n)
    (hf : CompactEigenvalueFinitenessInput.{0}) (hη : 0 < η)
    (X Y : MeasuredCompact.{0})
    (hX : dist (toGHSpace X) (toGHSpace X₀) < B.radius)
    (hY : dist (toGHSpace Y) (toGHSpace X₀) < B.radius)
    (e : X ≃ᵢ Y) (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs X : Measure X))]
    [StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs Y : Measure Y))] :
    (B.coordinateClass hf hη Y hY p).comap ⟨e, e.continuous⟩ =
      B.coordinateClass hf hη X hX p :=
  selectedSpectralCoordinateClass_comap hm hs hf X Y e η hη p hp n (B.rank X hX) (B.rank Y hY)

/-- A2 on the spectral neighborhood, with arbitrary representatives on both carriers. -/
theorem representative_equivariance (B : SpectralModelNeighborhood hm hs X₀ η n)
    (hf : CompactEigenvalueFinitenessInput.{0}) (hη : 0 < η)
    (X Y : MeasuredCompact.{0})
    (hX : dist (toGHSpace X) (toGHSpace X₀) < B.radius)
    (hY : dist (toGHSpace Y) (toGHSpace X₀) < B.radius)
    (e : X ≃ᵢ Y) (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs X : Measure X))]
    [StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs Y : Measure Y))]
    (a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin n)))
    (b : NormedCoordinatePair Y (EuclideanSpace ℝ (Fin n)))
    (ha : Quotient.mk _ a = B.coordinateClass hf hη X hX p)
    (hb : Quotient.mk _ b = B.coordinateClass hf hη Y hY p) :
    ∃ U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      (∀ x, b.coordinates (e x) = U (a.coordinates x)) ∧
      ∀ v, b.norm v = a.norm (U.symm v) :=
  coordinate_equivariance_of_comap_eq ⟨e, e.continuous⟩ _ _
    (B.coordinateClass_comap hf hη X Y hX hY e p hp) a b ha hb

end AmbientKernel.SpectralModelNeighborhood
end PaperN.PartII
