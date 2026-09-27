import PaperN.PartII.CoordinateDefinitions

namespace PaperN.Shared.Correspondence
variable {X Y X' Y' : Type*}

/-- Pull a correspondence back along equivalences of its two carriers. -/
def comapEquiv (R : Correspondence X Y) (e : X' ≃ X) (f : Y' ≃ Y) :
    Correspondence X' Y' where
  rel := {z | (e z.1, f z.2) ∈ R.rel}
  left_total x := by
    obtain ⟨y, hy⟩ := R.left_total (e x)
    exact ⟨f.symm y, by simpa using hy⟩
  right_total y := by
    obtain ⟨x, hx⟩ := R.right_total (f y)
    exact ⟨e.symm x, by simpa using hx⟩

/-- The relation points are reindexed bijectively, without closedness assumptions. -/
def comapEquivRel (R : Correspondence X Y) (e : X' ≃ X) (f : Y' ≃ Y) :
    (R.comapEquiv e f).rel ≃ R.rel where
  toFun z := ⟨(e z.val.1, f z.val.2), z.property⟩
  invFun z := ⟨(e.symm z.val.1, f.symm z.val.2), by simpa [comapEquiv] using z.property⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp

/-- Supremum errors over the relation are unchanged by carrier transport. -/
theorem iSup_comapEquiv (R : Correspondence X Y) (e : X' ≃ X) (f : Y' ≃ Y)
    (g : X → Y → ℝ) :
    (⨆ z : (R.comapEquiv e f).rel, g (e z.val.1) (f z.val.2)) =
      ⨆ z : R.rel, g z.val.1 z.val.2 :=
  (R.comapEquivRel e f).iSup_comp (g := fun z : R.rel ↦ g z.val.1 z.val.2)
end PaperN.Shared.Correspondence

namespace PaperN.PartII
open PaperN.Shared
/-- The A4 coordinate error is preserved when both maps and the relation are pulled back. -/
theorem coordinateError_comapEquiv {X Y X' Y' E : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    [NormedAddCommGroup E]
    (R : Correspondence X Y) (e : X' ≃ₜ X) (f : Y' ≃ₜ Y)
    (a : C(X, E)) (b : C(Y, E)) :
    coordinateError (R.comapEquiv e.toEquiv f.toEquiv)
      (a.comp ⟨e, e.continuous⟩) (b.comp ⟨f, f.continuous⟩) = coordinateError R a b := by
  exact R.iSup_comapEquiv e.toEquiv f.toEquiv (fun x y ↦ ‖a x - b y‖)
end PaperN.PartII
