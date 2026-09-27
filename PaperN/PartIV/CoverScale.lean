import PaperN.PartIV.EquilateralProducts

namespace PaperN.PartIV
open Set Metric
variable {X : Type*} [MetricSpace X]

/-- Truncated distance to the complement, with distance to the empty set treated as infinity. -/
noncomputable def coverClearance (U : Set X) (x : X) : ℝ := by
  classical
  exact if (Uᶜ).Nonempty then min 1 (infDist x Uᶜ) else 1

theorem coverClearance_bounds (U : Set X) (x : X) :
    0 ≤ coverClearance U x ∧ coverClearance U x ≤ 1 := by
  classical
  unfold coverClearance
  split_ifs
  · exact ⟨le_min zero_le_one infDist_nonneg, min_le_left _ _⟩
  · exact ⟨zero_le_one, le_rfl⟩

theorem coverClearance_lipschitz (U : Set X) : LipschitzWith 1 (coverClearance U) := by
  classical
  change LipschitzWith 1 (fun x ↦ coverClearance U x)
  by_cases h : (Uᶜ).Nonempty
  · simpa only [coverClearance, if_pos h] using (lipschitz_infDist_pt Uᶜ).const_min 1
  · simp only [coverClearance, if_neg h]
    exact (LipschitzWith.const 1).weaken (by norm_num)

theorem coverClearance_pos {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U) :
    0 < coverClearance U x := by
  classical
  unfold coverClearance
  split_ifs with h
  · exact lt_min zero_lt_one ((hU.isClosed_compl.notMem_iff_infDist_pos h).mp (by simpa using hx))
  · norm_num

/-- A ball smaller than clearance lies in the same open-set candidate. -/
theorem mem_of_dist_lt_coverClearance (U : Set X) (x y : X)
    (h : dist x y < coverClearance U x) : y ∈ U := by
  classical
  by_contra hy
  have hm : y ∈ Uᶜ := hy
  have hne : (Uᶜ).Nonempty := ⟨y, hm⟩
  have hd := infDist_le_dist_of_mem (x := x) hm
  simp only [coverClearance, if_pos hne] at h
  exact (not_lt_of_ge hd) (h.trans_le (min_le_right _ _))

variable {I : Type*} [Nonempty I]

/-- The supremum of the truncated clearances, scaled by 1/16. -/
noncomputable def coverScale (U : I → Set X) (x : X) : ℝ :=
  (⨆ i, coverClearance (U i) x) / 16

omit [Nonempty I] in
theorem coverClearance_bddAbove (U : I → Set X) (x : X) :
    BddAbove (range (fun i ↦ coverClearance (U i) x)) :=
  ⟨1, by rintro _ ⟨i, rfl⟩; exact (coverClearance_bounds _ _).2⟩

theorem coverScale_pos_le (U : I → Set X) (ho : ∀ i, IsOpen (U i))
    (hc : ∀ x, ∃ i, x ∈ U i) (x : X) : 0 < coverScale U x ∧ coverScale U x ≤ 1/16 := by
  obtain ⟨i, hi⟩ := hc x
  have hp := (coverClearance_pos (ho i) hi).trans_le (le_ciSup (coverClearance_bddAbove U x) i)
  have hu : (⨆ i, coverClearance (U i) x) ≤ 1 := ciSup_le (fun i ↦ (coverClearance_bounds _ _).2)
  unfold coverScale
  constructor <;> linarith

theorem coverScale_lipschitz (U : I → Set X) : LipschitzWith (1/16) (coverScale U) := by
  have hsup : LipschitzWith 1 (fun x ↦ ⨆ i, coverClearance (U i) x) := by
    apply LipschitzWith.of_le_add
    intro x y
    apply ciSup_le
    intro i
    have h := (coverClearance_lipschitz (U i)).dist_le_mul x y
    rw [Real.dist_eq] at h
    have hb := le_ciSup (coverClearance_bddAbove U y) i
    have hh := (le_abs_self (coverClearance (U i) x - coverClearance (U i) y)).trans h
    simp only [NNReal.coe_one, one_mul] at hh ⊢
    linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := hsup.dist_le_mul x y
  rw [Real.dist_eq] at h ⊢
  simp only [coverScale, ← sub_div, abs_div, abs_of_pos (by norm_num : (0:ℝ)<16)]
  norm_num at h ⊢
  linarith

/-- Any two points closer than the chosen scale belong to a common cover element. -/
theorem coverScale_subordinate (U : I → Set X) (ho : ∀ i, IsOpen (U i))
    (hc : ∀ x, ∃ i, x ∈ U i) (x y : X) (h : dist x y < coverScale U x) :
    ∃ i, x ∈ U i ∧ y ∈ U i := by
  have hp := (coverScale_pos_le U ho hc x).1
  have hd : dist x y < ⨆ i, coverClearance (U i) x := by
    unfold coverScale at h hp
    linarith
  obtain ⟨i, hi⟩ := exists_lt_of_lt_ciSup hd
  refine ⟨i, ?_, mem_of_dist_lt_coverClearance (U i) x y hi⟩
  apply mem_of_dist_lt_coverClearance (U i) x x
  simpa only [dist_self] using (dist_nonneg.trans_lt hi)

/-- The positive scale as a map into the positive real half-line. -/
noncomputable def positiveCoverScale (U : I → Set X) (ho : ∀ i, IsOpen (U i))
    (hc : ∀ x, ∃ i, x ∈ U i) (x : X) : Set.Ioi (0 : ℝ) :=
  ⟨coverScale U x, (coverScale_pos_le U ho hc x).1⟩

theorem positiveCoverScale_lipschitz (U : I → Set X) (ho : ∀ i, IsOpen (U i))
    (hc : ∀ x, ∃ i, x ∈ U i) : LipschitzWith (1/16) (positiveCoverScale U ho hc) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (coverScale_lipschitz U).dist_le_mul x y

open GromovHausdorff
/-- Finite equilateral approximation adapted to the specified open cover. -/
noncomputable def coverProduct (n : ℕ) [NeZero n] (U : I → Set GHSpace)
    (ho : ∀ i, IsOpen (U i)) (hc : ∀ x, ∃ i, x ∈ U i) (q : GHSpace) : GHSpace :=
  equilateralProduct n q (positiveCoverScale U ho hc q)

theorem coverProduct_lipschitz (n : ℕ) [NeZero n] (U : I → Set GHSpace)
    (ho : ∀ i, IsOpen (U i)) (hc : ∀ x, ∃ i, x ∈ U i) :
    LipschitzWith 1 (coverProduct n U ho hc) :=
  equilateralProduct_lipschitz n _ ((positiveCoverScale_lipschitz U ho hc).weaken (by norm_num [← NNReal.coe_le_coe]))

/-- The original and approximated GH classes lie together in a cover element. -/
theorem coverProduct_close (n : ℕ) [NeZero n] (U : I → Set GHSpace)
    (ho : ∀ i, IsOpen (U i)) (hc : ∀ x, ∃ i, x ∈ U i) (q : GHSpace) :
    ∃ i, q ∈ U i ∧ coverProduct n U ho hc q ∈ U i := by
  apply coverScale_subordinate U ho hc
  have h := equilateralProduct_error n q (positiveCoverScale U ho hc q)
  have hp := (coverScale_pos_le U ho hc q).1
  change dist (coverProduct n U ho hc q) q ≤ coverScale U q / 2 at h
  rw [dist_comm] at h
  linarith

end PaperN.PartIV
