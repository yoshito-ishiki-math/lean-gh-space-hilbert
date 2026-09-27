import PaperN.Shared.Statements
import PaperN.Shared.CorrespondenceEmbedding

namespace PaperN.Shared
open Set Metric GromovHausdorff
open scoped NNReal
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]


omit [Nonempty X] [Nonempty Y] in
theorem error_bdd (R : Correspondence X Y) (d : ContinuousPseudometric X)
    (e : ContinuousPseudometric Y) :
    BddAbove (range (fun z : R.rel × R.rel ↦ |d z.1.val.1 z.2.val.1 - e z.1.val.2 z.2.val.2|)) := by
  refine ⟨‖d.kernel‖ + ‖e.kernel‖, ?_⟩
  rintro _ ⟨z,rfl⟩
  exact (abs_sub _ _).trans (add_le_add
    (d.kernel.norm_coe_le_norm (z.1.val.1,z.2.val.1))
    (e.kernel.norm_coe_le_norm (z.1.val.2,z.2.val.2)))

omit [Nonempty X] [Nonempty Y] in
theorem le_error (R : Correspondence X Y) (d : ContinuousPseudometric X)
    (e : ContinuousPseudometric Y) (p q : R.rel) :
    |d p.val.1 q.val.1 - e p.val.2 q.val.2| ≤ correspondenceError R d e :=
  le_ciSup (error_bdd R d e) (p,q)

omit [Nonempty Y] in
theorem error_nonneg (R : Correspondence X Y) (d : ContinuousPseudometric X)
    (e : ContinuousPseudometric Y) : 0 ≤ correspondenceError R d e :=
  (abs_nonneg _).trans (le_error R d e (Classical.choice inferInstance) (Classical.choice inferInstance))

def quotientCorrespondence (R : Correspondence X Y) (d : ContinuousPseudometric X)
    (e : ContinuousPseudometric Y) : Correspondence d.Quotient e.Quotient where
  rel := (fun p : X × Y ↦ (d.proj p.1,e.proj p.2)) '' R.rel
  left_total x := by
    obtain ⟨a,rfl⟩ := d.proj_surjective x
    obtain ⟨b,hb⟩ := R.left_total a
    exact ⟨e.proj b, (a,b), hb, rfl⟩
  right_total y := by
    obtain ⟨b,rfl⟩ := e.proj_surjective y
    obtain ⟨a,ha⟩ := R.right_total b
    exact ⟨d.proj a, (a,b), ha, rfl⟩

/-- Q1, including pseudometrics which identify distinct points. -/
theorem quotient_ghDist_le (R : Correspondence X Y) (d : ContinuousPseudometric X)
    (e : ContinuousPseudometric Y) :
    ghDist d.Quotient e.Quotient ≤ correspondenceError R d e / 2 := by
  apply ghDist_le_half_distortion (quotientCorrespondence R d e)
  intro p q
  obtain ⟨a,ha,hpa⟩ := p.property
  obtain ⟨b,hb,hqb⟩ := q.property
  have h := le_error R d e ⟨a,ha⟩ ⟨b,hb⟩
  change |dist p.val.1 q.val.1 - dist p.val.2 q.val.2| ≤ _
  rw [← hpa, ← hqb]
  simpa only [d.dist_proj, e.dist_proj] using h

/-- Q4, uniform comparison on one carrier. -/
theorem quotient_ghDist_le_norm (d e : ContinuousPseudometric X) :
    ghDist d.Quotient e.Quotient ≤ ‖d.kernel - e.kernel‖ / 2 := by
  let R : Correspondence X X := ⟨{p | p.1 = p.2}, fun x ↦ ⟨x,rfl⟩, fun x ↦ ⟨x,rfl⟩⟩
  letI : Nonempty R.rel := ⟨⟨(Classical.choice (inferInstance : Nonempty X), Classical.choice (inferInstance : Nonempty X)), rfl⟩⟩
  apply (quotient_ghDist_le R d e).trans
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply ciSup_le
  intro z
  have h := (d.kernel - e.kernel).norm_coe_le_norm (z.1.val.1,z.2.val.1)
  have h1 : z.1.val.1 = z.1.val.2 := z.1.property
  have h2 : z.2.val.1 = z.2.val.2 := z.2.property
  simpa only [ContinuousMap.sub_apply, Real.norm_eq_abs, ← h1, ← h2] using h

/-- Q2, both coordinate projections are needed for comparison of uniform norms. -/
theorem uniform_norm_comparison (R : Correspondence X Y)
    (d₀ d₁ : ContinuousPseudometric X) (e₀ e₁ : ContinuousPseudometric Y) :
    |‖d₀.kernel - d₁.kernel‖ - ‖e₀.kernel - e₁.kernel‖| ≤
      correspondenceError R d₀ e₀ + correspondenceError R d₁ e₁ := by
  have pointwise (p q : R.rel) :
      |(d₀ p.val.1 q.val.1 - d₁ p.val.1 q.val.1) -
        (e₀ p.val.2 q.val.2 - e₁ p.val.2 q.val.2)| ≤
        correspondenceError R d₀ e₀ + correspondenceError R d₁ e₁ := by
    have h₀ := (abs_le.mp (le_error R d₀ e₀ p q))
    have h₁ := (abs_le.mp (le_error R d₁ e₁ p q))
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  apply abs_le.mpr
  constructor
  · have hb : ‖e₀.kernel-e₁.kernel‖ ≤ ‖d₀.kernel-d₁.kernel‖ +
        (correspondenceError R d₀ e₀ + correspondenceError R d₁ e₁) := by
      apply (ContinuousMap.norm_le_of_nonempty _).mpr
      intro y
      obtain ⟨x₀,h₀⟩ := R.right_total y.1
      obtain ⟨x₁,h₁⟩ := R.right_total y.2
      have hp := pointwise ⟨(x₀,y.1),h₀⟩ ⟨(x₁,y.2),h₁⟩
      have hn := (d₀.kernel-d₁.kernel).norm_coe_le_norm (x₀,x₁)
      change |e₀ y.1 y.2-e₁ y.1 y.2| ≤ _
      change |d₀ x₀ x₁-d₁ x₀ x₁| ≤ _ at hn
      dsimp at hp
      rcases abs_le.mp hp with ⟨hl,hu⟩
      rcases abs_le.mp hn with ⟨nl,nu⟩
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  · have hb : ‖d₀.kernel-d₁.kernel‖ ≤ ‖e₀.kernel-e₁.kernel‖ +
        (correspondenceError R d₀ e₀ + correspondenceError R d₁ e₁) := by
      apply (ContinuousMap.norm_le_of_nonempty _).mpr
      intro x
      obtain ⟨y₀,h₀⟩ := R.left_total x.1
      obtain ⟨y₁,h₁⟩ := R.left_total x.2
      have hp := pointwise ⟨(x.1,y₀),h₀⟩ ⟨(x.2,y₁),h₁⟩
      have hn := (e₀.kernel-e₁.kernel).norm_coe_le_norm (y₀,y₁)
      change |d₀ x.1 x.2-d₁ x.1 x.2| ≤ _
      change |e₀ y₀ y₁-e₁ y₀ y₁| ≤ _ at hn
      dsimp at hp
      rcases abs_le.mp hp with ⟨hl,hu⟩
      rcases abs_le.mp hn with ⟨nl,nu⟩
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    linarith

omit [Nonempty Y] in
/-- Q3, the endpoint parameters 0 and 1 are included. -/
theorem error_blend_le (R : Correspondence X Y)
    (d₀ d₁ : ContinuousPseudometric X) (e₀ e₁ : ContinuousPseudometric Y)
    (t : Set.Icc (0 : ℝ) 1) :
    correspondenceError R (d₀.blend d₁ t) (e₀.blend e₁ t) ≤
      (1-t.val) * correspondenceError R d₀ e₀ + t.val * correspondenceError R d₁ e₁ := by
  apply ciSup_le
  intro z
  have h₀ := abs_le.mp (le_error R d₀ e₀ z.1 z.2)
  have h₁ := abs_le.mp (le_error R d₁ e₁ z.1 z.2)
  change |((1-t.val)*d₀ z.1.val.1 z.2.val.1+t.val*d₁ z.1.val.1 z.2.val.1) -
    ((1-t.val)*e₀ z.1.val.2 z.2.val.2+t.val*e₁ z.1.val.2 z.2.val.2)| ≤ _
  have ht₀ := t.property.1
  have ht₁ := t.property.2
  apply abs_le.mpr
  constructor
  · have hA := mul_le_mul_of_nonneg_left h₀.1 (sub_nonneg.mpr ht₁)
    have hB := mul_le_mul_of_nonneg_left h₁.1 ht₀
    nlinarith
  · have hA := mul_le_mul_of_nonneg_left h₀.2 (sub_nonneg.mpr ht₁)
    have hB := mul_le_mul_of_nonneg_left h₁.2 ht₀
    nlinarith

theorem pseudometricComparison_spec : PseudometricComparisonStatement.{u,v} := by
  intro X Y _ _ _ _ _ _ R d₀ d₁ e₀ e₁
  exact ⟨quotient_ghDist_le R d₀ e₀, uniform_norm_comparison R d₀ d₁ e₀ e₁,
    error_blend_le R d₀ d₁ e₀ e₁, quotient_ghDist_le_norm d₀ d₁⟩
end PaperN.Shared
