import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Finite.Lemmas

namespace PaperN.PartIV

/-- The functions appearing in the non-Archimedean GH function model. -/
structure UrysohnFunction where
  value : NNReal → ℕ
  zero : value 0 = 0
  finite_tail : ∀ ε : NNReal, 0 < ε → {r | ε ≤ r ∧ value r ≠ 0}.Finite

instance : CoeFun UrysohnFunction (fun _ ↦ NNReal → ℕ) := ⟨UrysohnFunction.value⟩

@[ext] theorem UrysohnFunction.ext {f g : UrysohnFunction}
    (h : ∀ r, f r = g r) : f = g := by
  cases f
  cases g
  congr
  exact funext h

/-- Disagreement also has finite tails, being contained in the union of supports. -/
theorem UrysohnFunction.finite_disagreement_tail (f g : UrysohnFunction)
    (ε : NNReal) (hε : 0 < ε) : {r | ε ≤ r ∧ f r ≠ g r}.Finite := by
  apply ((f.finite_tail ε hε).union (g.finite_tail ε hε)).subset
  intro r hr
  by_cases hf : f r = 0
  · exact Or.inr ⟨hr.1, fun hg ↦ hr.2 (hf.trans hg.symm)⟩
  · exact Or.inl ⟨hr.1, hf⟩

/-- Distinct functions have a greatest disagreement coordinate, necessarily positive. -/
theorem UrysohnFunction.exists_greatest_disagreement (f g : UrysohnFunction)
    (hfg : f ≠ g) : ∃ r : NNReal, 0 < r ∧ f r ≠ g r ∧ ∀ s, f s ≠ g s → s ≤ r := by
  have hw : ∃ r, f r ≠ g r := by
    by_contra h
    apply hfg
    ext r
    exact Classical.not_not.mp (fun hn ↦ h ⟨r, hn⟩)
  obtain ⟨ε, hε⟩ := hw
  have hpos : 0 < ε := by
    apply lt_of_le_of_ne (zero_le : 0 ≤ ε)
    intro he
    subst ε
    exact hε (f.zero.trans g.zero.symm)
  obtain ⟨r, hr, hmax⟩ := Set.exists_max_image _ (fun r : NNReal ↦ r) (f.finite_disagreement_tail g ε hpos) ⟨ε, le_rfl, hε⟩
  refine ⟨r, hpos.trans_le hr.1, hr.2, ?_⟩
  intro s hs
  by_cases h : ε ≤ s
  · exact hmax s ⟨h, hs⟩
  · exact (le_of_not_ge h).trans hr.1

/-- Maximum disagreement, with zero on the diagonal. -/
noncomputable def UrysohnFunction.distance (f g : UrysohnFunction) : NNReal :=
  open Classical in
  if h : f = g then 0 else (f.exists_greatest_disagreement g h).choose

@[simp] theorem UrysohnFunction.distance_self (f : UrysohnFunction) : f.distance f = 0 := by
  simp [distance]

theorem UrysohnFunction.distance_spec (f g : UrysohnFunction) (h : f ≠ g) :
    0 < f.distance g ∧ f (f.distance g) ≠ g (f.distance g) ∧
      ∀ s, f s ≠ g s → s ≤ f.distance g := by
  simpa only [distance, dif_neg h] using (f.exists_greatest_disagreement g h).choose_spec

theorem UrysohnFunction.le_distance (f g : UrysohnFunction) (s : NNReal)
    (hs : f s ≠ g s) : s ≤ f.distance g :=
  (f.distance_spec g (fun h ↦ hs (congrArg (fun k : UrysohnFunction ↦ k s) h))).2.2 s hs

theorem UrysohnFunction.distance_le (f g : UrysohnFunction) (r : NNReal)
    (h : ∀ s, f s ≠ g s → s ≤ r) : f.distance g ≤ r := by
  by_cases he : f = g
  · subst g
    simp
  · exact h _ (f.distance_spec g he).2.1

theorem UrysohnFunction.distance_comm (f g : UrysohnFunction) :
    f.distance g = g.distance f := by
  apply le_antisymm
  · exact f.distance_le g _ (fun s hs ↦ g.le_distance f s (Ne.symm hs))
  · exact g.distance_le f _ (fun s hs ↦ f.le_distance g s (Ne.symm hs))

theorem UrysohnFunction.distance_eq_zero_iff (f g : UrysohnFunction) :
    f.distance g = 0 ↔ f = g := by
  constructor
  · intro h
    by_contra he
    have := (f.distance_spec g he).1
    simp [h] at this
  · rintro rfl
    exact f.distance_self

/-- Strong triangle inequality for the manuscript's maximum-disagreement formula. -/
theorem UrysohnFunction.distance_ultrametric (f g h : UrysohnFunction) :
    f.distance h ≤ max (f.distance g) (g.distance h) := by
  apply f.distance_le h
  intro s hs
  by_cases he : f s = g s
  · exact (g.le_distance h s (fun hh ↦ hs (he.trans hh))).trans (le_max_right _ _)
  · exact (f.le_distance g s he).trans (le_max_left _ _)

end PaperN.PartIV
