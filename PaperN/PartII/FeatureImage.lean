import PaperN.PartII.WeightedPseudometric

namespace PaperN.PartII
open PaperN.Shared TopologicalSpace GromovHausdorff Set
variable {X E : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X] [MetricSpace E]

/-- The nonempty compact image of a continuous feature on a compact carrier. -/
def featureImage (f : X → E) (hf : Continuous f) : NonemptyCompacts E :=
  ⟨⟨range f, isCompact_range hf⟩, range_nonempty f⟩

/-- A feature realizing a pseudometric has the same GH class as its separated quotient. -/
theorem featureImage_gh_eq (f : X → E) (hf : Continuous f)
    (d : ContinuousPseudometric X) (hd : ∀ x y, dist (f x) (f y) = d x y) :
    (featureImage f hf).toGHSpace = d.gh := by
  let K := featureImage f hf
  let R : Correspondence d.Quotient K := {
    rel := {z | ∃ x : X, z.1 = d.proj x ∧ z.2.val = f x}
    left_total := by
      intro q
      obtain ⟨x, rfl⟩ := d.proj_surjective q
      exact ⟨⟨f x, mem_range_self x⟩, x, rfl, rfl⟩
    right_total := by
      rintro ⟨y, x, rfl⟩
      exact ⟨d.proj x, x, rfl, rfl⟩ }
  apply Eq.symm
  apply dist_le_zero.mp
  change ghDist d.Quotient K ≤ 0
  have h : ghDist d.Quotient K ≤ (0 : ℝ) / 2 := by
    apply ghDist_le_half_distortion R
    intro u v
    obtain ⟨x, hx, hy⟩ := u.property
    obtain ⟨y, hz, hw⟩ := v.property
    change |dist u.val.1 v.val.1 - dist u.val.2.val v.val.2.val| ≤ 0
    rw [hx, hz, hy, hw, d.dist_proj, hd]
    simp
  simpa only [zero_div] using h

/-- The correspondence above yields an actual isometry of the separated quotient and image. -/
theorem featureImage_quotient_isometry (f : X → E) (hf : Continuous f)
    (d : ContinuousPseudometric X) (hd : ∀ x y, dist (f x) (f y) = d x y) :
    Nonempty (d.Quotient ≃ᵢ featureImage f hf) :=
  toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp (featureImage_gh_eq f hf d hd).symm

variable {I : Type*} [DecidableEq I] {B : I → Type*}
    [∀ i, NormedAddCommGroup (B i)] [∀ i, NormedSpace ℝ (B i)]

/-- The compact image of the finite block feature. -/
noncomputable def finiteFeatureImage (s : Finset I) (w : I → ℝ) (f : ∀ i, X → B i)
    (hf : ∀ i ∈ s, Continuous (f i)) : NonemptyCompacts (lp B 1) :=
  featureImage (fun x ↦ finiteBlockFeature s w (fun i ↦ f i x))
    (continuous_finiteBlockFeature s w f hf)

/-- The feature image represents the weighted pseudometric quotient. -/
theorem finiteFeatureImage_gh_eq (s : Finset I) (w : I → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (f : ∀ i, X → B i)
    (hf : ∀ i ∈ s, Continuous (f i)) (d : I → ContinuousPseudometric X)
    (hd : ∀ i ∈ s, ∀ x y, dist (f i x) (f i y) = d i x y) :
    (finiteFeatureImage s w f hf).toGHSpace = (weightedPseudometric s w hw d).gh :=
  featureImage_gh_eq _ _ _ (finiteBlockFeature_dist_eq_weighted s w hw d f hd)

/-- The actual compact feature image satisfies the strict approximation bound. -/
theorem finiteFeatureImage_ghDist_lt (s : Finset I) (w : I → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1)
    (f : ∀ i, X → B i) (hf : ∀ i ∈ s, Continuous (f i))
    (d : I → ContinuousPseudometric X)
    (hd : ∀ i ∈ s, ∀ x y, dist (f i x) (f i y) = d i x y)
    (c : ContinuousPseudometric X) (ε : ℝ)
    (he : ∀ i ∈ s, 0 < w i → ‖c.kernel - (d i).kernel‖ < ε) :
    dist c.gh (finiteFeatureImage s w f hf).toGHSpace < ε / 2 := by
  rw [finiteFeatureImage_gh_eq s w hw f hf d hd]
  exact weightedPseudometric_ghDist_lt s w hw hs d c ε he

end PaperN.PartII
