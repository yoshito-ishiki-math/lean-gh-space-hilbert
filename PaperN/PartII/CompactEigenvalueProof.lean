import PaperN.PartII.CompactEigenvalueInput
import Mathlib.Analysis.Normed.Module.RCLike.Real

namespace PaperN.PartII
open Set Metric

/-- Compact self-adjoint operators have finitely many eigenvalues beyond a positive threshold. -/
theorem compact_selfAdjoint_finite_large_eigenvalues
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H) (hc : IsCompactOperator T) (ha : IsSelfAdjoint T)
    (η : ℝ) (hη : 0 < η) :
    Set.Finite {a : ℝ | η < |a| ∧ Module.End.HasEigenvalue T.toLinearMap a} := by
  classical
  let A := {a : ℝ | η < |a| ∧ Module.End.HasEigenvalue T.toLinearMap a}
  have hu (a : A) : ∃ v : Module.End.eigenspace T.toLinearMap a.val, ‖v‖ = 1 := by
    letI : Nontrivial (Module.End.eigenspace T.toLinearMap a.val) :=
      Submodule.nontrivial_iff_ne_bot.mpr a.property.2
    exact exists_norm_eq _ (by norm_num : (0 : ℝ) ≤ 1)
  choose v hv using hu
  have he (a : A) : T (v a : H) = a.val • (v a : H) :=
    (Module.End.mem_eigenspace_iff.mp (v a).property)
  have hn (a : A) : ‖T (v a : H)‖ = |a.val| := by
    rw [he, norm_smul, Real.norm_eq_abs]
    change |a.val| * ‖v a‖ = _
    rw [hv, mul_one]
  have hsep (a b : A) (hab : a ≠ b) : η ≤ dist (T (v a : H)) (T (v b : H)) := by
    have ho : inner ℝ (v a : H) (v b : H) = 0 :=
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp ha).orthogonalFamily_eigenspaces
        (fun h ↦ hab (Subtype.ext h)) (v a) (v b)
    have hot : inner ℝ (T (v a : H)) (T (v b : H)) = 0 := by
      rw [he, he, inner_smul_left, inner_smul_right, ho]
      simp
    have hs := norm_sub_sq_real (T (v a : H)) (T (v b : H))
    rw [hot, hn, hn] at hs
    rw [dist_eq_norm]
    have := a.property.1
    nlinarith [norm_nonneg (T (v a : H) - T (v b : H)), sq_nonneg |b.val|]
  obtain ⟨K, hK, hsub⟩ := hc.image_closedBall_subset_compact 1
  have hmem (a : A) : T (v a : H) ∈ K := by
    apply hsub
    refine ⟨(v a : H), ?_, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    change ‖v a‖ ≤ 1
    exact le_of_eq (hv a)
  obtain ⟨S, hS, hcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded
    (η / 3) (by positivity)
  letI := hS.to_subtype
  have hex (a : A) : ∃ c : S, dist (T (v a : H)) c < η / 3 := by
    have h := hcover (hmem a)
    simp only [mem_iUnion, mem_ball] at h
    obtain ⟨c, hc, hd⟩ := h
    exact ⟨⟨c, hc⟩, hd⟩
  let f : A → S := fun a ↦ (hex a).choose
  have hi : Function.Injective f := by
    intro a b hab
    by_contra hne
    have h₁ := (hex a).choose_spec
    have h₂ := (hex b).choose_spec
    change dist (T (v a : H)) (f a) < η / 3 at h₁
    change dist (T (v b : H)) (f b) < η / 3 at h₂
    rw [← hab] at h₂
    have ht := dist_triangle (T (v a : H)) (f a : H) (T (v b : H))
    rw [dist_comm (f a : H)] at ht
    have := hsep a b hne
    linarith
  letI := Finite.of_injective f hi
  exact Set.toFinite A

/-- The previously cited finite-eigenvalue input is now proved at every universe. -/
theorem compactEigenvalueFinitenessInput_proved : CompactEigenvalueFinitenessInput := by
  intro H _ _ _ T hc ha η hη
  exact compact_selfAdjoint_finite_large_eigenvalues T hc ha η hη

end PaperN.PartII
