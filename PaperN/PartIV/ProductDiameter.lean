import PaperN.PartIV.DiameterNormalization

namespace PaperN.PartIV
open PaperN.Shared GromovHausdorff Set Metric

/-- Diameter of a nonempty compact max product. -/
theorem diam_univ_prod (X Y : Type*) [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y] :
    diam (univ : Set (X × Y)) = max (diam (univ : Set X)) (diam (univ : Set Y)) := by
  apply le_antisymm
  · apply diam_le_of_forall_dist_le (le_max_of_le_left diam_nonneg)
    intro p _ q _
    rw [Prod.dist_eq]
    exact max_le_max
      (dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _))
      (dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _))
  · apply max_le
    · let y : Y := Classical.choice inferInstance
      have hi : Isometry (fun x : X ↦ (x,y)) := Isometry.of_dist_eq (by simp)
      have h := diam_mono (subset_univ (range (fun x : X ↦ (x,y))))
        (isCompact_univ : IsCompact (univ : Set (X × Y))).isBounded
      simpa only [hi.diam_range] using h
    · let x : X := Classical.choice inferInstance
      have hi : Isometry (fun y : Y ↦ (x,y)) := Isometry.of_dist_eq (by simp)
      have h := diam_mono (subset_univ (range (fun y : Y ↦ (x,y))))
        (isCompact_univ : IsCompact (univ : Set (X × Y))).isBounded
      simpa only [hi.diam_range] using h

/-- The diameter formula on GH classes. -/
theorem ghDiameter_productGH (q r : GHSpace) :
    ghDiameter (productGH q r) = max (ghDiameter q) (ghDiameter r) := by
  rw [productGH, ghDiameter_toGHSpace, diam_univ_prod]
  rfl

/-- A singleton right factor does not change the GH class. -/
theorem productGH_point_right (q : GHSpace) : productGH q pointGH = q := by
  have he : Isometry (Prod.fst : q.Rep × Unit → q.Rep) :=
    Isometry.of_dist_eq (by intro x y; simp [Prod.dist_eq])
  have hs : Function.Surjective (Prod.fst : q.Rep × Unit → q.Rep) := fun x ↦ ⟨(x,()),rfl⟩
  have h := toGHSpace_eq_toGHSpace_iff_isometryEquiv.mpr
    ⟨(⟨Equiv.ofBijective Prod.fst ⟨he.injective,hs⟩,he⟩ : q.Rep × Unit ≃ᵢ q.Rep)⟩
  simpa only [← productGH_toGHSpace, GHSpace.toGHSpace_rep, pointGH] using h

/-- A singleton left factor does not change the GH class. -/
theorem productGH_point_left (q : GHSpace) : productGH pointGH q = q := by
  have he : Isometry (Prod.snd : Unit × q.Rep → q.Rep) :=
    Isometry.of_dist_eq (by intro x y; simp [Prod.dist_eq])
  have hs : Function.Surjective (Prod.snd : Unit × q.Rep → q.Rep) := fun x ↦ ⟨((),x),rfl⟩
  have h := toGHSpace_eq_toGHSpace_iff_isometryEquiv.mpr
    ⟨(⟨Equiv.ofBijective Prod.snd ⟨he.injective,hs⟩,he⟩ : Unit × q.Rep ≃ᵢ q.Rep)⟩
  simpa only [← productGH_toGHSpace, GHSpace.toGHSpace_rep, pointGH] using h

/-- A two-point equilateral space witnesses nonemptiness of the diameter-one locus. -/
theorem unitDiameter_nonempty : Nonempty UnitDiameterSpace := by
  let s : Ioi (0 : ℝ) := ⟨1, by norm_num⟩
  refine ⟨⟨toGHSpace (Equilateral 2 s), ?_⟩⟩
  rw [ghDiameter_toGHSpace]
  apply le_antisymm
  · apply diam_le_of_forall_dist_le (by norm_num)
    intro x _ y _
    rw [equilateral_dist]
    split_ifs <;> norm_num [s]
  · have h := dist_le_diam_of_mem
      (isCompact_univ : IsCompact (univ : Set (Equilateral 2 s))).isBounded
      (mem_univ (show Equilateral 2 s from (0 : Fin 2)))
      (mem_univ (show Equilateral 2 s from (1 : Fin 2)))
    rw [equilateral_dist, if_neg (show (show Equilateral 2 s from (0 : Fin 2)) ≠
      (show Equilateral 2 s from (1 : Fin 2)) from by
        change (0 : Fin 2) ≠ 1
        decide)] at h
    exact h

end PaperN.PartIV
