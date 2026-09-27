import PaperN.PartIV.LocallyFiniteProducts

namespace PaperN.PartIV
open PaperN.Shared GromovHausdorff Set Metric

/-- Diameter of the canonical compact representative. -/
noncomputable def ghDiameter (q : GHSpace) : ℝ := diam (univ : Set q.Rep)

/-- Diameter is independent of the representative. -/
theorem ghDiameter_toGHSpace (X : Type*) [MetricSpace X] [CompactSpace X] [Nonempty X] :
    ghDiameter (toGHSpace X) = diam (univ : Set X) := by
  obtain ⟨e⟩ := toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp
    (GHSpace.toGHSpace_rep (toGHSpace X))
  have h := e.isometry.diam_range
  rw [e.surjective.range_eq] at h
  exact h.symm

/-- Distortion bounds the change of diameter. -/
theorem diameter_le_of_distortion {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y] (R : Correspondence X Y) (a : ℝ)
    (ha : 0 ≤ a) (hR : R.DistortionLE a) :
    diam (univ : Set X) ≤ diam (univ : Set Y) + a := by
  apply diam_le_of_forall_dist_le (add_nonneg diam_nonneg ha)
  intro x _ x' _
  obtain ⟨y, hy⟩ := R.left_total x
  obtain ⟨y', hy'⟩ := R.left_total x'
  have hb := (le_abs_self (dist x x' - dist y y')).trans
    (hR ⟨(x,y), hy⟩ ⟨(x',y'), hy'⟩)
  have hd := dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ y) (mem_univ y')
  linarith

/-- Diameter is 2-Lipschitz in Gromov--Hausdorff distance. -/
theorem ghDiameter_lipschitz : LipschitzWith 2 ghDiameter := by
  apply LipschitzWith.of_dist_le_mul
  intro q z
  have bound (q z : GHSpace) : ghDiameter q ≤ ghDiameter z + 2 * dist q z := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨R, hR⟩ := exists_correspondence_distortion q.Rep z.Rep
      (dist q z + ε/2) (by simpa only [ghDist, GHSpace.toGHSpace_rep] using
        (show dist q z < dist q z + ε/2 by linarith))
    have hb := diameter_le_of_distortion R _ (by positivity) hR
    change ghDiameter q ≤ ghDiameter z + 2 * (dist q z + ε/2) at hb
    linarith
  rw [Real.dist_eq, abs_le]
  have h₁ := bound q z
  have h₂ := bound z q
  rw [dist_comm z q] at h₂
  norm_num
  constructor <;> linarith

/-- A max product with a factor of diameter at most one preserves diameter one. -/
theorem diam_prod_eq_one (X Y : Type*) [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty Y]
    (hX : diam (univ : Set X) = 1) (hY : diam (univ : Set Y) ≤ 1) :
    diam (univ : Set (X × Y)) = 1 := by
  apply le_antisymm
  · apply diam_le_of_forall_dist_le (by norm_num)
    intro x _ y _
    rw [Prod.dist_eq]
    exact max_le ((dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)).trans hX.le)
      ((dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)).trans hY)
  · let y : Y := Classical.choice inferInstance
    have hi : Isometry (fun x : X ↦ (x,y)) := Isometry.of_dist_eq (by simp)
    have hm := diam_mono (subset_univ (range (fun x : X ↦ (x,y))))
      (isCompact_univ : IsCompact (univ : Set (X × Y))).isBounded
    rw [hi.diam_range, hX] at hm
    exact hm

/-- Every cover-adapted product map preserves the diameter-one locus. -/
theorem cardApprox_diameter_one {I : Type*} [Nonempty I] (U : I → Set GHSpace)
    (ho : ∀ i, IsOpen (U i)) (hc : ∀ q, ∃ i, q ∈ U i)
    (a : ℕ+) (q : GHSpace) (hq : ghDiameter q = 1) :
    ghDiameter (cardApprox a U ho hc q) = 1 := by
  letI : NeZero a.val := ⟨a.ne_zero⟩
  let s := positiveCoverScale U ho hc q
  have heq : cardApprox a U ho hc q = toGHSpace (q.Rep × Equilateral a.val s) := by
    simpa only [GHSpace.toGHSpace_rep, cardApprox, coverProduct, equilateralProduct, s] using productGH_toGHSpace q.Rep (Equilateral a.val s)
  rw [heq, ghDiameter_toGHSpace]
  apply diam_prod_eq_one _ _ hq
  apply diam_le_of_forall_dist_le (by norm_num)
  intro x _ y _
  rw [equilateral_dist]
  have hs : s.val ≤ 1 := le_trans (coverScale_pos_le U ho hc q).2 (by norm_num)
  split_ifs
  · norm_num
  · exact hs

end PaperN.PartIV
