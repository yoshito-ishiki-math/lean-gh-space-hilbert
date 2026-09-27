import PaperN.PartII.NormedCoordinateClass

namespace PaperN.PartII
variable {X Y Z E : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pull back the coordinate map while retaining its coordinate norm. -/
def NormedCoordinatePair.comap (f : C(X, Y)) (a : NormedCoordinatePair Y E) :
    NormedCoordinatePair X E where
  coordinates := a.coordinates.comp f
  norm := a.norm
  definite := a.definite

theorem NormedCoordinatePair.equivalent_comap (f : C(X, Y))
    {a b : NormedCoordinatePair Y E} (h : a.Equivalent b) :
    (a.comap f).Equivalent (b.comap f) := by
  obtain ⟨U, hc, hn⟩ := h
  exact ⟨U, fun x ↦ hc (f x), hn⟩

/-- Carrier pullback is independent of the orthogonal representative. -/
def NormedCoordinateClass.comap (f : C(X, Y)) (a : NormedCoordinateClass Y E) :
    NormedCoordinateClass X E :=
  Quotient.map (NormedCoordinatePair.comap f)
    (fun _ _ h ↦ NormedCoordinatePair.equivalent_comap f h) a

@[simp] theorem NormedCoordinateClass.comap_mk (f : C(X, Y)) (a : NormedCoordinatePair Y E) :
    NormedCoordinateClass.comap f (Quotient.mk _ a : NormedCoordinateClass Y E) = Quotient.mk _ (a.comap f) := rfl

@[simp] theorem NormedCoordinateClass.value_comap (f : C(X, Y))
    (a : NormedCoordinateClass Y E) (x : X) : (a.comap f).value x = a.value (f x) := by
  induction a using Quotient.inductionOn with
  | h a => rfl

@[simp] theorem NormedCoordinateClass.pseudometric_comap_apply [FiniteDimensional ℝ E]
    (f : C(X, Y)) (a : NormedCoordinateClass Y E) (x y : X) :
    (NormedCoordinateClass.pseudometric X E (a.comap f)) x y =
      (NormedCoordinateClass.pseudometric Y E a) (f x) (f y) := by
  induction a using Quotient.inductionOn with
  | h a => rfl

@[simp] theorem NormedCoordinateClass.comap_id (a : NormedCoordinateClass X E) :
    a.comap (ContinuousMap.id X) = a := by
  induction a using Quotient.inductionOn with
  | h a => rfl

@[simp] theorem NormedCoordinateClass.comap_comp (f : C(X, Y)) (g : C(Y, Z))
    (a : NormedCoordinateClass Z E) : a.comap (g.comp f) = (a.comap g).comap f := by
  induction a using Quotient.inductionOn with
  | h a => rfl

/-- A homeomorphism changes the carrier without changing the coordinate-class data. -/
def NormedCoordinateClass.comapEquiv (e : X ≃ₜ Y) :
    NormedCoordinateClass Y E ≃ NormedCoordinateClass X E where
  toFun := comap ⟨e, e.continuous⟩
  invFun := comap ⟨e.symm, e.symm.continuous⟩
  left_inv := by
    intro a
    rw [← comap_comp]
    have he : (⟨e, e.continuous⟩ : C(X, Y)).comp ⟨e.symm, e.symm.continuous⟩ = ContinuousMap.id Y := by
      ext y
      exact e.apply_symm_apply y
    rw [he, comap_id]
  right_inv := by
    intro a
    rw [← comap_comp]
    have he : (⟨e.symm, e.symm.continuous⟩ : C(Y, X)).comp ⟨e, e.continuous⟩ = ContinuousMap.id X := by
      ext x
      exact e.symm_apply_apply x
    rw [he, comap_id]

end PaperN.PartII
