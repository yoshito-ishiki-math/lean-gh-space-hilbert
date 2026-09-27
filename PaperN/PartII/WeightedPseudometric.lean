import PaperN.PartII.FiniteBlockFeature
import PaperN.Shared.PseudometricComparison

namespace PaperN.PartII
open PaperN.Shared GromovHausdorff
variable {I X : Type*} [TopologicalSpace X]

/-- A finite nonnegative combination of continuous pseudometrics. -/
noncomputable def weightedPseudometric (s : Finset I) (w : I → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (d : I → ContinuousPseudometric X) :
    ContinuousPseudometric X where
  kernel := ∑ i ∈ s, w i • (d i).kernel
  self x := by simp [ContinuousMap.sum_apply, (d _).self]
  comm x y := by
    simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun i _ ↦ congrArg (w i * ·) ((d i).comm x y))
  triangle x y z := by
    simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i hi ↦ by
      simpa only [mul_add] using mul_le_mul_of_nonneg_left ((d i).triangle x y z) (hw i hi))

@[simp] theorem weightedPseudometric_apply (s : Finset I) (w : I → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (d : I → ContinuousPseudometric X) (x y : X) :
    weightedPseudometric s w hw d x y = ∑ i ∈ s, w i * d i x y := by
  simp [weightedPseudometric, ContinuousMap.sum_apply]

/-- The uniform error is bounded by the average local error. -/
theorem weightedPseudometric_error_le [CompactSpace X]
    (s : Finset I) (w : I → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hs : ∑ i ∈ s, w i = 1) (d : I → ContinuousPseudometric X)
    (c : ContinuousPseudometric X) :
    ‖c.kernel - (weightedPseudometric s w hw d).kernel‖ ≤
      ∑ i ∈ s, w i * ‖c.kernel - (d i).kernel‖ := by
  have he : c.kernel - (weightedPseudometric s w hw d).kernel =
      ∑ i ∈ s, w i • (c.kernel - (d i).kernel) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hs, one_smul,
      weightedPseudometric]
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_smul, Real.norm_of_nonneg (hw i hi)]

/-- Strict local error bounds imply a strict global bound, including zero weights. -/
theorem weightedPseudometric_error_lt [CompactSpace X]
    (s : Finset I) (w : I → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hs : ∑ i ∈ s, w i = 1) (d : I → ContinuousPseudometric X)
    (c : ContinuousPseudometric X) (ε : ℝ)
    (he : ∀ i ∈ s, 0 < w i → ‖c.kernel - (d i).kernel‖ < ε) :
    ‖c.kernel - (weightedPseudometric s w hw d).kernel‖ < ε := by
  have hp : ∃ i ∈ s, 0 < w i :=
    (Finset.sum_pos_iff_of_nonneg hw).mp (by rw [hs]; norm_num)
  apply (weightedPseudometric_error_le s w hw hs d c).trans_lt
  calc
    ∑ i ∈ s, w i * ‖c.kernel - (d i).kernel‖ < ∑ i ∈ s, w i * ε := by
      apply Finset.sum_lt_sum
      · intro i hi
        by_cases h : w i = 0
        · simp [h]
        · exact (mul_lt_mul_of_pos_left (he i hi (lt_of_le_of_ne (hw i hi) (Ne.symm h)))
            (lt_of_le_of_ne (hw i hi) (Ne.symm h))).le
      · obtain ⟨i, hi, hpos⟩ := hp
        exact ⟨i, hi, mul_lt_mul_of_pos_left (he i hi hpos) hpos⟩
    _ = ε := by rw [← Finset.sum_mul, hs, one_mul]

/-- Separated compact quotients have at most half the averaged error in GH distance. -/
theorem weightedPseudometric_ghDist_le [CompactSpace X] [Nonempty X]
    (s : Finset I) (w : I → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hs : ∑ i ∈ s, w i = 1) (d : I → ContinuousPseudometric X)
    (c : ContinuousPseudometric X) :
    dist c.gh (weightedPseudometric s w hw d).gh ≤
      (∑ i ∈ s, w i * ‖c.kernel - (d i).kernel‖) / 2 :=
  (quotient_ghDist_le_norm c (weightedPseudometric s w hw d)).trans
    (div_le_div_of_nonneg_right (weightedPseudometric_error_le s w hw hs d c) (by norm_num))

/-- Strict uniform approximation passes to GH distance. -/
theorem weightedPseudometric_ghDist_lt [CompactSpace X] [Nonempty X]
    (s : Finset I) (w : I → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hs : ∑ i ∈ s, w i = 1) (d : I → ContinuousPseudometric X)
    (c : ContinuousPseudometric X) (ε : ℝ)
    (he : ∀ i ∈ s, 0 < w i → ‖c.kernel - (d i).kernel‖ < ε) :
    dist c.gh (weightedPseudometric s w hw d).gh < ε / 2 :=
  (quotient_ghDist_le_norm c (weightedPseudometric s w hw d)).trans_lt
    (div_lt_div_of_pos_right (weightedPseudometric_error_lt s w hw hs d c ε he) (by norm_num))

/-- Realizing each local pseudometric by a block realizes their weighted sum. -/
theorem finiteBlockFeature_dist_eq_weighted [DecidableEq I] {B : I → Type*}
    [∀ i, NormedAddCommGroup (B i)] [∀ i, NormedSpace ℝ (B i)]
    (s : Finset I) (w : I → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (d : I → ContinuousPseudometric X) (f : ∀ i, X → B i)
    (hf : ∀ i ∈ s, ∀ x y, dist (f i x) (f i y) = d i x y) (x y : X) :
    dist (finiteBlockFeature s w (fun i ↦ f i x))
      (finiteBlockFeature s w (fun i ↦ f i y)) = weightedPseudometric s w hw d x y := by
  rw [finiteBlockFeature_dist s w hw, weightedPseudometric_apply]
  exact Finset.sum_congr rfl (fun i hi ↦ congrArg (w i * ·) (hf i hi x y))

end PaperN.PartII
