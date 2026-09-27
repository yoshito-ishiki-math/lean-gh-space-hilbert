import PaperN.PartII.ResolventStrongConvergence

namespace PaperN.PartII

/-- Quantitative stability of invertibility with a prescribed bound on the inverse. -/
theorem isUnit_and_inverse_norm_le_of_near
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (T S : E →L[ℂ] E) (ht : IsUnit T) (B : ℝ) (hB : 0 ≤ B)
    (hi : ‖Ring.inverse T‖ ≤ B) (hd : B * ‖S - T‖ < 1 / 2) :
    IsUnit S ∧ ‖Ring.inverse S‖ ≤ 2 * B := by
  let R := Ring.inverse T
  have hRT : R * T = 1 := Ring.inverse_mul_cancel T ht
  have hTR : T * R = 1 := Ring.mul_inverse_cancel T ht
  have hn : ‖R * (T - S)‖ < 1 := by
    have h := norm_mul_le R (T - S)
    rw [norm_sub_rev T S] at h
    have hb := mul_le_mul_of_nonneg_right hi (norm_nonneg (S - T))
    dsimp [R] at h
    linarith
  have hu := isUnit_one_sub_of_norm_lt_one hn
  have hid : T * (1 - R * (T - S)) = S := by
    rw [mul_sub, mul_one, ← mul_assoc, hTR, one_mul]
    abel
  have hS : IsUnit S := hid ▸ ht.mul hu
  refine ⟨hS, inverse_norm_le_of_lowerBound S hS (2 * B) (by positivity) ?_⟩
  intro x
  have hRx : R (T x) = x := congrArg (fun A : E →L[ℂ] E ↦ A x) hRT
  have hx : ‖x‖ ≤ B * ‖T x‖ := by
    calc
      ‖x‖ = ‖R (T x)‖ := congrArg norm hRx.symm
      _ ≤ ‖R‖ * ‖T x‖ := R.le_opNorm _
      _ ≤ B * ‖T x‖ := mul_le_mul_of_nonneg_right hi (norm_nonneg _)
  have he : ‖T x‖ ≤ ‖S x‖ + ‖S - T‖ * ‖x‖ := by
    calc
      ‖T x‖ = ‖S x - (S - T) x‖ := by congr 1; simp
      _ ≤ ‖S x‖ + ‖(S - T) x‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add le_rfl ((S - T).le_opNorm x)
  have hh := mul_le_mul_of_nonneg_left he hB
  have hn0 := norm_nonneg x
  have hm : (B * ‖S - T‖) * ‖x‖ ≤ (1 / 2 : ℝ) * ‖x‖ :=
    mul_le_mul_of_nonneg_right hd.le hn0
  nlinarith
end PaperN.PartII
