import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace PaperN.PartI
variable {X : Type*} [MetricSpace X]

/-- Rouyer's total anisometry: distances distinguish unordered pairs of distinct points. -/
def TotallyAnisometric (X : Type*) [MetricSpace X] : Prop :=
  ∀ a b c d : X, a ≠ b → c ≠ d → dist a b = dist c d →
    (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- Three points suffice; the two-point exception must not be omitted. -/
theorem isometry_eq_id_of_totallyAnisometric
    (h : TotallyAnisometric X)
    (hthree : ∀ x : X, ∃ y z : X, x ≠ y ∧ x ≠ z ∧ y ≠ z)
    {f : X → X} (hf : Isometry f) : f = id := by
  funext x
  obtain ⟨y, z, hxy, hxz, hyz⟩ := hthree x
  have h₁ := h (f x) (f y) x y (hf.injective.ne hxy) hxy (hf.dist_eq x y)
  have h₂ := h (f x) (f z) x z (hf.injective.ne hxz) hxz (hf.dist_eq x z)
  change f x = x
  rcases h₁ with h₁ | h₁
  · exact h₁.1
  rcases h₂ with h₂ | h₂
  · exact h₂.1
  exact (hyz (h₁.1.symm.trans h₂.1)).elim

/-- The infinite case applies in particular to nonempty perfect metric spaces. -/
theorem isometry_eq_id_of_infinite_totallyAnisometric [Infinite X]
    (h : TotallyAnisometric X) {f : X → X} (hf : Isometry f) : f = id := by
  apply isometry_eq_id_of_totallyAnisometric h _ hf
  intro x
  classical
  obtain ⟨y, hy⟩ := exists_ne x
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset ({x, y} : Finset X)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
  exact ⟨y, z, hy.symm, Ne.symm hz.1, Ne.symm hz.2⟩

/-- No surjectivity assumption is needed for the rigidity argument above. -/
theorem subsingleton_isometryEquiv_of_infinite_totallyAnisometric [Infinite X]
    (h : TotallyAnisometric X) : Subsingleton (X ≃ᵢ X) := by
  constructor
  intro f g
  have hf := isometry_eq_id_of_infinite_totallyAnisometric h f.isometry
  have hg := isometry_eq_id_of_infinite_totallyAnisometric h g.isometry
  ext x
  exact congrFun (hf.trans hg.symm) x

/-- A map constant on a dense set is discontinuous wherever it takes a different value.
This is the topological step in the isometry-group discontinuity argument. -/
theorem not_continuousAt_of_dense_constant {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [T1Space B]
    {S : Set A} (hS : Dense S) {f : A → B} {c : B}
    (hc : ∀ x ∈ S, f x = c) {x : A} (hx : f x ≠ c) :
    ¬ ContinuousAt f x := by
  intro hf
  have hm := mem_closure_image hf (hS x)
  have hs : f '' S ⊆ {c} := by
    rintro _ ⟨y, hy, rfl⟩
    exact hc y hy
  have := closure_mono hs hm
  rw [isClosed_singleton.closure_eq] at this
  exact hx this

end PaperN.PartI
