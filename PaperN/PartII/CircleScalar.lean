import Mathlib.Analysis.Complex.CauchyIntegral

namespace PaperN.PartII
open Complex Metric Set
open scoped Real

noncomputable def scalarCircle (a c : ℂ) (r : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ • circleIntegral (fun z ↦ (z-a)⁻¹) c r

theorem scalarCircle_inside (a c : ℂ) (r : ℝ) (ha : a ∈ ball c r) :
    scalarCircle a c r = 1 := by
  simpa [scalarCircle] using
    (Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      (f := fun _ : ℂ ↦ (1 : ℂ)) (s := ∅) countable_empty ha continuousOn_const
      (fun _ _ ↦ differentiableAt_const (1 : ℂ)))

theorem scalarCircle_outside (a c : ℂ) (r : ℝ) (hr : 0 ≤ r) (ha : a ∉ closedBall c r) :
    scalarCircle a c r = 0 := by
  have hn : ∀ z ∈ closedBall c r, z-a ≠ 0 := by
    intro z hz he
    exact ha (sub_eq_zero.mp he ▸ hz)
  have hc : ContinuousOn (fun z : ℂ ↦ (z-a)⁻¹) (closedBall c r) :=
    (continuousOn_id.sub continuousOn_const).inv₀ hn
  have hd : ∀ z ∈ ball c r \ (∅ : Set ℂ), DifferentiableAt ℂ (fun z : ℂ ↦ (z-a)⁻¹) z := by
    intro z hz
    exact (differentiableAt_id.sub_const a).inv (hn z (ball_subset_closedBall hz.1))
  have h := Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr
    countable_empty hc hd
  simp [scalarCircle, h]
theorem scalarCircle_real_interval_inside (a l r : ℝ) (hal : l < a) (har : a < r) :
    scalarCircle (a : ℂ) (((l+r)/2 : ℝ) : ℂ) ((r-l)/2) = 1 := by
  apply scalarCircle_inside
  rw [mem_ball, Complex.isometry_ofReal.dist_eq]
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem scalarCircle_real_interval_outside (a l r : ℝ) (hlr : l ≤ r)
    (ha : a < l ∨ r < a) :
    scalarCircle (a : ℂ) (((l+r)/2 : ℝ) : ℂ) ((r-l)/2) = 0 := by
  apply scalarCircle_outside _ _ _ (by linarith)
  rw [mem_closedBall, Complex.isometry_ofReal.dist_eq, Real.dist_eq]
  intro hh
  have hh' := abs_le.mp hh
  rcases ha with h | h <;> linarith [hh'.1, hh'.2]
theorem scalarCircle_cutoff_pair (a η B : ℝ) (hη : 0 < η) (hB : η < B)
    (hb : |a| < B) (hp : a ≠ η) (hn : a ≠ -η) :
    scalarCircle (a : ℂ) (((η+B)/2 : ℝ) : ℂ) ((B-η)/2) +
      scalarCircle (a : ℂ) (((-B + -η)/2 : ℝ) : ℂ) ((-η - -B)/2) =
      if η < |a| then 1 else 0 := by
  have hab := abs_lt.mp hb
  by_cases hpos : η < a
  · rw [scalarCircle_real_interval_inside a η B hpos hab.2,
      scalarCircle_real_interval_outside a (-B) (-η) (by linarith) (Or.inr (by linarith))]
    rw [if_pos (hpos.trans_le (le_abs_self a))]; simp
  by_cases hneg : a < -η
  · rw [scalarCircle_real_interval_outside a η B (le_of_lt hB) (Or.inl (by linarith)),
      scalarCircle_real_interval_inside a (-B) (-η) hab.1 hneg]
    rw [if_pos (lt_of_lt_of_le (by linarith : η < -a) (neg_le_abs a))]; simp
  · have ha₁ : a < η := lt_of_le_of_ne (le_of_not_gt hpos) hp
    have ha₂ : -η < a := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hn)
    rw [scalarCircle_real_interval_outside a η B (le_of_lt hB) (Or.inl ha₁),
      scalarCircle_real_interval_outside a (-B) (-η) (by linarith) (Or.inr ha₂)]
    rw [if_neg (not_lt.mpr (abs_le.mpr ⟨le_of_lt ha₂, le_of_lt ha₁⟩))]; simp
end PaperN.PartII
