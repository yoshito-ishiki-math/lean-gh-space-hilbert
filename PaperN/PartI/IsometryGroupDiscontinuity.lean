import PaperN.PartI.IsometryGroupGH
import PaperN.PartIV.EquilateralProducts

namespace PaperN.PartI
open GromovHausdorff PaperN.PartIV

/-- Every permutation of an equilateral carrier is an isometry. -/
noncomputable def equilateralPermutation (n : ℕ) (s : Set.Ioi (0 : ℝ))
    (e : Equiv.Perm (Equilateral n s)) : Equilateral n s ≃ᵢ Equilateral n s where
  toEquiv := e
  isometry_toFun := Isometry.of_dist_eq fun x y ↦ by
    change dist (e x) (e y) = dist x y
    simp only [equilateral_dist, e.injective.eq_iff]

/-- The two-point space has a nontrivial self-isometry, with no cited input. -/
theorem twoPoint_isometryGroup_nontrivial :
    ¬ Subsingleton (Equilateral 2 ⟨1, by norm_num⟩ ≃ᵢ Equilateral 2 ⟨1, by norm_num⟩) := by
  intro h
  letI := h
  let s : Set.Ioi (0 : ℝ) := ⟨1, by norm_num⟩
  let a : Equilateral 2 s := (0 : Fin 2)
  let b : Equilateral 2 s := (1 : Fin 2)
  have he := Subsingleton.elim (equilateralPermutation 2 s (Equiv.swap a b))
    (IsometryEquiv.refl (Equilateral 2 s))
  have hv := congrArg (fun e : Equilateral 2 s ≃ᵢ Equilateral 2 s ↦ e a) he
  have hab : a ≠ b := by
    change (0 : Fin 2) ≠ 1
    decide
  change (Equiv.swap a b) a = a at hv
  rw [Equiv.swap_apply_left] at hv
  exact hab hv.symm

/-- A concrete representative's symmetry implies discontinuity at its GH class. -/
theorem isometryGroupGH_not_continuousAt_concrete (hR : RouyerGenericInput)
    (X : Type*) [MetricSpace X] [CompactSpace X] [Nonempty X]
    (hX : ¬ Subsingleton (X ≃ᵢ X)) :
    ¬ ContinuousAt isometryGroupGH (toGHSpace X) := by
  apply isometryGroupGH_discontinuous_of_rouyer hR
  intro h
  letI := h
  obtain ⟨e⟩ := toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp
    (GHSpace.toGHSpace_rep (toGHSpace X))
  exact hX (isometryGroupConjugacy e).symm.injective.subsingleton

/-- The global noncontinuity asserted in Part I's introduction. -/
theorem isometryGroupGH_not_continuous (hR : RouyerGenericInput) :
    ¬ Continuous isometryGroupGH := by
  intro h
  exact isometryGroupGH_not_continuousAt_concrete hR
    (Equilateral 2 ⟨1, by norm_num⟩) twoPoint_isometryGroup_nontrivial h.continuousAt

end PaperN.PartI
