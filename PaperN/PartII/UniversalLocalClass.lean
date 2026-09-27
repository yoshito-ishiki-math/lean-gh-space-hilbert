import PaperN.PartII.CoordinateEquivariance
import PaperN.PartII.LocalModel
import PaperN.PartI.UniverseAssignment

namespace PaperN.PartII
open PaperN.PartI GromovHausdorff
namespace LocalModel
variable {X₀ : MeasuredCompact.{0}} {τ : ℝ} (M : LocalModel X₀ τ)

/-- The A2 witness gives equality of coordinate classes under carrier pullback. -/
theorem coordinateClass_comap (X Y : MeasuredCompact.{0})
    (hX : toGHSpace X ∈ M.domain) (hY : toGHSpace Y ∈ M.domain) (e : X ≃ᵢ Y) :
    (M.coordinateClass Y hY).comap ⟨e, e.continuous⟩ = M.coordinateClass X hX := by
  obtain ⟨a, ha⟩ := Quotient.exists_rep (M.coordinateClass X hX)
  obtain ⟨b, hb⟩ := Quotient.exists_rep (M.coordinateClass Y hY)
  rw [← ha, ← hb, NormedCoordinateClass.comap_mk]
  apply Quotient.sound
  apply NormedCoordinatePair.equivalent_symm
  obtain ⟨U, hu, hn⟩ := M.equivariance X Y hX hY e a b ha hb
  refine ⟨U, hu, ?_⟩
  intro v
  change b.norm (U v) = a.norm v
  simpa only [U.symm_apply_apply] using hn (U v)

/-- One small local model supplies coordinate classes on arbitrary-universe carriers. -/
noncomputable def universalClass (X : Type*) [MetricSpace X] [CompactSpace X] [Nonempty X]
    (hX : toGHSpace X ∈ M.domain) : NormedCoordinateClass X (EuclideanSpace ℝ (Fin M.dimension)) :=
  (M.coordinateClass (smallCarrier X) (by
    simpa only [smallCarrier, ghRepresentative_class] using hX)).comap
      ⟨(smallCarrierEquiv X).symm, (smallCarrierEquiv X).symm.continuous⟩

/-- The universal class is independent of the small representative and its identifying isometry. -/
theorem universalClass_eq_comap (X : Type*) [MetricSpace X] [CompactSpace X] [Nonempty X]
    (hX : toGHSpace X ∈ M.domain) (Y : MeasuredCompact.{0})
    (hY : toGHSpace Y ∈ M.domain) (e : X ≃ᵢ Y) :
    M.universalClass X hX = (M.coordinateClass Y hY).comap ⟨e, e.continuous⟩ := by
  let k := (smallCarrierEquiv X).trans e
  have hs : toGHSpace (smallCarrier X) ∈ M.domain := by
    simpa only [smallCarrier, ghRepresentative_class] using hX
  have h := M.coordinateClass_comap (smallCarrier X) Y hs hY k
  unfold universalClass
  rw [← h, ← NormedCoordinateClass.comap_comp]
  congr 1
  ext x
  exact congrArg e ((smallCarrierEquiv X).apply_symm_apply x)

/-- The coordinate-value bound transports to every concrete carrier. -/
theorem universalClass_bound (X : Type*) [MetricSpace X] [CompactSpace X] [Nonempty X]
    (hX : toGHSpace X ∈ M.domain) (x : X) :
    (M.universalClass X hX).value x ≤ 2 * Metric.diam (Set.univ : Set X) := by
  have hs : toGHSpace (smallCarrier X) ∈ M.domain := by
    simpa only [smallCarrier, ghRepresentative_class] using hX
  obtain ⟨a, ha⟩ := Quotient.exists_rep (M.coordinateClass (smallCarrier X) hs)
  have hb := M.bound (smallCarrier X) hs a ha ((smallCarrierEquiv X).symm x)
  have hd := (smallCarrierEquiv X).isometry.diam_image (Set.univ : Set (smallCarrier X))
  rw [Set.image_univ_of_surjective (smallCarrierEquiv X).surjective] at hd
  unfold universalClass
  rw [NormedCoordinateClass.value_comap, ← ha, NormedCoordinateClass.value_mk]
  change a.norm (a.coordinates ((smallCarrierEquiv X).symm x)) ≤ _
  rw [hd]
  exact hb

/-- Naturality holds between concrete carriers in independently chosen universes. -/
theorem universalClass_comap (X Y : Type*) [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    (hX : toGHSpace X ∈ M.domain) (hY : toGHSpace Y ∈ M.domain) (e : X ≃ᵢ Y) :
    (M.universalClass Y hY).comap ⟨e, e.continuous⟩ = M.universalClass X hX := by
  have hs : toGHSpace (smallCarrier Y) ∈ M.domain := by
    simpa only [smallCarrier, ghRepresentative_class] using hY
  rw [M.universalClass_eq_comap X hX (smallCarrier Y) hs
    (e.trans (smallCarrierEquiv Y).symm)]
  unfold universalClass
  rw [← NormedCoordinateClass.comap_comp]
  rfl

/-- A2 for arbitrary representatives of the transported classes. -/
theorem universalClass_equivariance (X Y : Type*) [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    (hX : toGHSpace X ∈ M.domain) (hY : toGHSpace Y ∈ M.domain) (e : X ≃ᵢ Y)
    (a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin M.dimension)))
    (b : NormedCoordinatePair Y (EuclideanSpace ℝ (Fin M.dimension)))
    (ha : Quotient.mk _ a = M.universalClass X hX)
    (hb : Quotient.mk _ b = M.universalClass Y hY) :
    ∃ U : EuclideanSpace ℝ (Fin M.dimension) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin M.dimension),
      (∀ x, b.coordinates (e x) = U (a.coordinates x)) ∧
      (∀ v, b.norm v = a.norm (U.symm v)) := by
  have h := M.universalClass_comap X Y hX hY e
  rw [← ha, ← hb, NormedCoordinateClass.comap_mk] at h
  have he := NormedCoordinatePair.equivalent_symm (Quotient.exact h)
  obtain ⟨U, hu, hn⟩ := he
  refine ⟨U, hu, ?_⟩
  intro v
  have hh := hn (U.symm v)
  change b.norm (U (U.symm v)) = a.norm (U.symm v) at hh
  simpa only [U.apply_symm_apply] using hh

/-- The same GH-space error is the metric error of every universal representative. -/
theorem universalClass_error_eq (X : Type*) [MetricSpace X] [CompactSpace X] [Nonempty X]
    (hX : toGHSpace X ∈ M.domain)
    (a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin M.dimension)))
    (ha : Quotient.mk _ a = M.universalClass X hX) :
    M.error (toGHSpace X) = ⨆ z : X × X, |a.pseudometric z.1 z.2 - dist z.1 z.2| := by
  have hs : toGHSpace (smallCarrier X) ∈ M.domain := by
    simpa only [smallCarrier, ghRepresentative_class] using hX
  obtain ⟨b, hb⟩ := Quotient.exists_rep (M.coordinateClass (smallCarrier X) hs)
  have he := M.error_eq (smallCarrier X) hs b hb
  simp only [smallCarrier, ghRepresentative_class] at he
  rw [he]
  have h := coordinate_metric_error_eq_of_comap_eq
    (smallCarrierEquiv X).symm (M.universalClass X hX)
    (M.coordinateClass (smallCarrier X) hs) rfl
  rw [← ha, ← hb] at h
  exact h.symm

/-- A6 for every pair of representatives, on independently chosen carrier universes. -/
theorem universalClass_pseudometric_invariant (X Y : Type*)
    [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    (hX : toGHSpace X ∈ M.domain) (hY : toGHSpace Y ∈ M.domain) (e : X ≃ᵢ Y)
    (a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin M.dimension)))
    (b : NormedCoordinatePair Y (EuclideanSpace ℝ (Fin M.dimension)))
    (ha : Quotient.mk _ a = M.universalClass X hX)
    (hb : Quotient.mk _ b = M.universalClass Y hY) (x y : X) :
    b.pseudometric (e x) (e y) = a.pseudometric x y := by
  have h := M.universalClass_comap X Y hX hY e
  have hp := NormedCoordinateClass.pseudometric_comap_apply
    ⟨e, e.continuous⟩ (M.universalClass Y hY) x y
  rw [h, ← ha, ← hb] at hp
  exact hp.symm

/-- A3 stated directly for every representative of the universal class. -/
theorem universalClass_representative_bound (X : Type*)
    [MetricSpace X] [CompactSpace X] [Nonempty X]
    (hX : toGHSpace X ∈ M.domain)
    (a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin M.dimension)))
    (ha : Quotient.mk _ a = M.universalClass X hX) (x : X) :
    a.norm (a.coordinates x) ≤ 2 * Metric.diam (Set.univ : Set X) := by
  have h := M.universalClass_bound X hX x
  rw [← ha] at h
  exact h

end LocalModel
end PaperN.PartII
