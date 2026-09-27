import PaperN.PartII.CoordinateDefinitions

namespace PaperN.PartII
open PaperN.Shared
variable (X E : Type*) [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A coordinate map and an actual norm, represented as a definite seminorm. -/
structure NormedCoordinatePair where
  coordinates : C(X, E)
  norm : Seminorm ℝ E
  definite : ∀ v, norm v = 0 → v = 0

namespace NormedCoordinatePair
variable {X E}

def Equivalent (a b : NormedCoordinatePair X E) : Prop :=
  ∃ U : E ≃ₗᵢ[ℝ] E, (∀ x, b.coordinates x = U (a.coordinates x)) ∧
    ∀ v, b.norm (U v) = a.norm v

theorem equivalent_refl (a : NormedCoordinatePair X E) : Equivalent a a :=
  ⟨LinearIsometryEquiv.refl ℝ E, fun _ ↦ rfl, fun _ ↦ rfl⟩

theorem equivalent_symm {a b : NormedCoordinatePair X E} (h : Equivalent a b) : Equivalent b a := by
  obtain ⟨U, hc, hn⟩ := h
  refine ⟨U.symm, ?_, ?_⟩
  · intro x
    rw [hc, U.symm_apply_apply]
  · intro v
    simpa using (hn (U.symm v)).symm

theorem equivalent_trans {a b c : NormedCoordinatePair X E}
    (hab : Equivalent a b) (hbc : Equivalent b c) : Equivalent a c := by
  obtain ⟨U, hu, hn⟩ := hab
  obtain ⟨V, hv, hm⟩ := hbc
  refine ⟨U.trans V, ?_, ?_⟩
  · intro x
    simpa using (hv x).trans (congrArg V (hu x))
  · intro v
    exact (hm (U v)).trans (hn v)

instance setoid : Setoid (NormedCoordinatePair X E) where
  r := Equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

variable [FiniteDimensional ℝ E]

noncomputable def pseudometric (a : NormedCoordinatePair X E) : ContinuousPseudometric X :=
  coordinatePseudometric a.norm (seminorm_continuous_finiteDimensional a.norm) a.coordinates

theorem pseudometric_eq_of_equivalent {a b : NormedCoordinatePair X E} (h : Equivalent a b) :
    a.pseudometric = b.pseudometric := by
  obtain ⟨U, hc, hn⟩ := h
  have hk : a.pseudometric.kernel = b.pseudometric.kernel := by
    ext p
    change a.norm (a.coordinates p.1 - a.coordinates p.2) = b.norm (b.coordinates p.1 - b.coordinates p.2)
    rw [hc, hc, ← U.map_sub, hn]
  have hi : Function.Injective (ContinuousPseudometric.kernel (X := X)) := by
    intro p q h
    cases p
    cases q
    cases h
    rfl
  exact hi hk

omit [FiniteDimensional ℝ E] in
theorem norm_coordinates_eq_of_equivalent {a b : NormedCoordinatePair X E} (h : Equivalent a b)
    (x : X) : a.norm (a.coordinates x) = b.norm (b.coordinates x) := by
  obtain ⟨U, hc, hn⟩ := h
  rw [hc, hn]

end NormedCoordinatePair

abbrev NormedCoordinateClass := Quotient (NormedCoordinatePair.setoid (X := X) (E := E))

noncomputable def NormedCoordinateClass.pseudometric [FiniteDimensional ℝ E]
    (a : NormedCoordinateClass X E) : ContinuousPseudometric X :=
  Quotient.lift NormedCoordinatePair.pseudometric
    (fun _ _ h ↦ NormedCoordinatePair.pseudometric_eq_of_equivalent h) a

end PaperN.PartII

namespace PaperN.PartII.NormedCoordinateClass
open PaperN.Shared
variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def value (a : NormedCoordinateClass X E) (x : X) : ℝ :=
  Quotient.lift (fun p : NormedCoordinatePair X E ↦ p.norm (p.coordinates x))
    (fun _ _ h ↦ NormedCoordinatePair.norm_coordinates_eq_of_equivalent h x) a

@[simp] theorem value_mk (a : NormedCoordinatePair X E) (x : X) :
    value (Quotient.mk _ a) x = a.norm (a.coordinates x) := rfl

@[simp] theorem pseudometric_mk [FiniteDimensional ℝ E]
    (a : NormedCoordinatePair X E) :
    pseudometric X E (Quotient.mk _ a) = a.pseudometric := rfl

end PaperN.PartII.NormedCoordinateClass
