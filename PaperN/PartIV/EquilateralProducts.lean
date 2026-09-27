import PaperN.PartIV.MetricProducts

namespace PaperN.PartIV
open PaperN.Shared GromovHausdorff

/-- A finite labelled carrier with a positive equilateral scale. -/
def Equilateral (n : ℕ) (_s : Set.Ioi (0 : ℝ)) := Fin n

instance (n : ℕ) (s : Set.Ioi (0 : ℝ)) : DecidableEq (Equilateral n s) :=
  inferInstanceAs (DecidableEq (Fin n))

instance (n : ℕ) (s : Set.Ioi (0 : ℝ)) : Finite (Equilateral n s) :=
  inferInstanceAs (Finite (Fin n))
instance (n : ℕ) [NeZero n] (s : Set.Ioi (0 : ℝ)) : Nonempty (Equilateral n s) :=
  inferInstanceAs (Nonempty (Fin n))

noncomputable instance equilateralMetric (n : ℕ) (s : Set.Ioi (0 : ℝ)) :
    MetricSpace (Equilateral n s) where
  dist x y := if x = y then 0 else s.val
  dist_self x := by simp
  dist_comm x y := by simp only [eq_comm]
  dist_triangle x y z := by
    have hs : 0 < s.val := s.property
    split_ifs <;> simp_all <;> linarith
  eq_of_dist_eq_zero := by
    intro x y h
    split_ifs at h with he
    · exact he
    · exact False.elim (ne_of_gt s.property h)

/-- Distances between distinct labels equal the prescribed scale. -/
theorem equilateral_dist (n : ℕ) (s : Set.Ioi (0 : ℝ)) (x y : Equilateral n s) :
    dist x y = if x = y then 0 else s.val := rfl

/-- Equal labels at different scales give a sharp GH estimate. -/
theorem equilateral_ghDist_le (n : ℕ) [NeZero n] (s t : Set.Ioi (0 : ℝ)) :
    ghDist (Equilateral n s) (Equilateral n t) ≤ |s.val - t.val| / 2 := by
  let R : Correspondence (Equilateral n s) (Equilateral n t) := {
    rel := {p | (show Fin n from p.1) = (show Fin n from p.2)}
    left_total x := ⟨x, rfl⟩
    right_total y := ⟨y, rfl⟩ }
  apply ghDist_le_half_distortion R _
  intro p q
  have hp : (show Fin n from p.val.1) = p.val.2 := p.property
  have hq : (show Fin n from q.val.1) = q.val.2 := q.property
  change |(if p.val.1 = q.val.1 then 0 else s.val) -
    (if p.val.2 = q.val.2 then 0 else t.val)| ≤ _
  have he : p.val.1 = q.val.1 ↔ p.val.2 = q.val.2 := by
    exact ⟨fun h ↦ hp.symm.trans (h.trans hq), fun h ↦ hp.trans (h.trans hq.symm)⟩
  simp only [he]
  split_ifs <;> simp

/-- The equilateral-product approximation, with variable positive scale. -/
noncomputable def equilateralProduct (n : ℕ) [NeZero n]
    (q : GHSpace) (s : Set.Ioi (0 : ℝ)) : GHSpace :=
  productGH q (toGHSpace (Equilateral n s))

/-- The projection correspondence bounds the approximation error by half the scale. -/
theorem equilateralProduct_error (n : ℕ) [NeZero n] (q : GHSpace) (s : Set.Ioi (0 : ℝ)) :
    dist (equilateralProduct n q s) q ≤ s.val / 2 := by
  let R : Correspondence (q.Rep × Equilateral n s) q.Rep := {
    rel := {p | p.1.1 = p.2}
    left_total x := ⟨x.1, rfl⟩
    right_total x := ⟨(x, Classical.choice inferInstance), rfl⟩ }
  have hs : 0 < s.val := s.property
  have h := ghDist_le_half_distortion R s.val (by
    intro p r
    have hp : p.val.1.1 = p.val.2 := p.property
    have hr : r.val.1.1 = r.val.2 := r.property
    change |max (dist p.val.1.1 r.val.1.1) (dist p.val.1.2 r.val.1.2) -
      dist p.val.2 r.val.2| ≤ s.val
    rw [hp, hr, equilateral_dist]
    split_ifs
    · rw [max_eq_left dist_nonneg, sub_self, abs_zero]
      exact s.property.le
    · rw [abs_of_nonneg (sub_nonneg.mpr (le_max_left _ _))]
      have hd : 0 ≤ dist p.val.2 r.val.2 := dist_nonneg
      exact sub_le_iff_le_add.mpr (max_le (by linarith) (by linarith)))
  have he := productGH_toGHSpace q.Rep (Equilateral n s)
  rw [GHSpace.toGHSpace_rep] at he
  simpa only [equilateralProduct, he, ghDist, GHSpace.toGHSpace_rep] using h

/-- Varying the space and the equilateral scale obeys the sharp max estimate. -/
theorem equilateralProduct_dist_le (n : ℕ) [NeZero n]
    (q r : GHSpace) (s t : Set.Ioi (0 : ℝ)) :
    dist (equilateralProduct n q s) (equilateralProduct n r t) ≤
      max (dist q r) (|s.val - t.val| / 2) :=
  (productGH_dist_le _ _ _ _).trans
    (max_le_max le_rfl (equilateral_ghDist_le n s t))

/-- A 2-Lipschitz positive scale makes the product approximation 1-Lipschitz. -/
theorem equilateralProduct_lipschitz (n : ℕ) [NeZero n]
    (s : GHSpace → Set.Ioi (0 : ℝ)) (hs : LipschitzWith 2 s) :
    LipschitzWith 1 (fun q ↦ equilateralProduct n q (s q)) := by
  apply LipschitzWith.of_dist_le_mul
  intro q r
  have hscale := hs.dist_le_mul q r
  change |(s q).val - (s r).val| ≤ 2 * dist q r at hscale
  have h := equilateralProduct_dist_le n q r (s q) (s r)
  simp only [NNReal.coe_one, one_mul]
  exact h.trans (max_le le_rfl (by linarith))

/-- A fiber contains all labels at pairwise distance equal to the scale. -/
theorem equilateralProduct_fiber_dist (n : ℕ) (s : Set.Ioi (0 : ℝ))
    {X : Type*} [MetricSpace X] (x : X) (i j : Equilateral n s) (hij : i ≠ j) :
    dist (x, i) (x, j) = s.val := by
  simp only [Prod.dist_eq, dist_self, equilateral_dist, if_neg hij]
  exact max_eq_right s.property.le

end PaperN.PartIV
