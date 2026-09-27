import PaperN.PartI.LawAveragingStatements
import PaperN.PartI.Valov
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

namespace PaperN.PartI
open MeasureTheory
open scoped BoundedContinuousFunction
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

/-- Integrating against a weakly continuous law gives a bounded continuous function. -/
noncomputable def lawAverage (s : C(Y, ProbabilityMeasure X)) (f : X →ᵇ ℝ) : Y →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun y ↦ ∫ x, f x ∂(s y : Measure X))
    ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp s.continuous)
    ‖f‖ (fun y ↦ f.norm_integral_le_norm (s y : Measure X))

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem lawAverage_norm_le (s : C(Y, ProbabilityMeasure X)) (f : X →ᵇ ℝ) :
    ‖lawAverage s f‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
    (fun y ↦ f.norm_integral_le_norm (s y : Measure X))

noncomputable def lawAveragingOperator (s : C(Y, ProbabilityMeasure X)) :
    (X →ᵇ ℝ) →L[ℝ] (Y →ᵇ ℝ) :=
  LinearMap.mkContinuous {
    toFun := lawAverage s
    map_add' := fun f g ↦ by
      ext y
      exact integral_add (f.integrable _) (g.integrable _)
    map_smul' := fun a f ↦ by
      ext y
      exact integral_smul a _ } 1 (fun f ↦ by simpa using lawAverage_norm_le s f)

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem lawAveragingOperator_positive (s : C(Y, ProbabilityMeasure X))
    (f : X →ᵇ ℝ) (hf : 0 ≤ f) : 0 ≤ lawAveragingOperator s f := by
  intro y
  exact integral_nonneg (fun x ↦ hf x)

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem lawAveragingOperator_one (s : C(Y, ProbabilityMeasure X)) :
    lawAveragingOperator s 1 = 1 := by
  ext y
  change (∫ _ : X, (1 : ℝ) ∂(s y : Measure X)) = 1
  simp

theorem lawAveragingOperator_pullback (p : C(X, Y)) (s : C(Y, ProbabilityMeasure X))
    (hs : ∀ y, probabilityPushforward p (s y) = diracProba y) (f : Y →ᵇ ℝ) :
    lawAveragingOperator s (f.compContinuous p) = f := by
  ext y
  have h := congrArg ProbabilityMeasure.toMeasure (hs y)
  change Measure.map p (s y : Measure X) = Measure.dirac y at h
  change (∫ x, f (p x) ∂(s y : Measure X)) = f y
  rw [← integral_map p.continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable, h]
  exact integral_dirac' f y f.continuous.measurable.stronglyMeasurable

/-- Pullback after averaging is a bounded linear projection onto the pullback range. -/
noncomputable def lawAveragingProjection (p : C(X, Y)) (s : C(Y, ProbabilityMeasure X)) :
    (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ) :=
  LinearMap.mkContinuous {
    toFun := fun f ↦ (lawAveragingOperator s f).compContinuous p
    map_add' := fun f g ↦ by simp [map_add, BoundedContinuousFunction.add_compContinuous]
    map_smul' := fun a f ↦ by ext x; simp } 1 (fun f ↦ by
      simpa using ((lawAveragingOperator s f).norm_compContinuous_le p).trans (lawAverage_norm_le s f))

theorem lawAveragingProjection_idempotent (p : C(X, Y)) (s : C(Y, ProbabilityMeasure X))
    (hs : ∀ y, probabilityPushforward p (s y) = diracProba y) (f : X →ᵇ ℝ) :
    lawAveragingProjection p s (lawAveragingProjection p s f) = lawAveragingProjection p s f := by
  change (lawAveragingOperator s ((lawAveragingOperator s f).compContinuous p)).compContinuous p = _
  rw [lawAveragingOperator_pullback p s hs]
  rfl

theorem lawAveragingProjection_range (p : C(X, Y)) (s : C(Y, ProbabilityMeasure X))
    (hs : ∀ y, probabilityPushforward p (s y) = diracProba y) :
    Set.range (lawAveragingProjection p s) = Set.range (fun f : Y →ᵇ ℝ ↦ f.compContinuous p) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨lawAveragingOperator s g, rfl⟩
  · rintro ⟨g, rfl⟩
    refine ⟨g.compContinuous p, ?_⟩
    change (lawAveragingOperator s (g.compContinuous p)).compContinuous p = _
    rw [lawAveragingOperator_pullback p s hs]

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem lawAveragingProjection_norm [Nonempty X] (p : C(X, Y)) (s : C(Y, ProbabilityMeasure X)) :
    ‖lawAveragingProjection p s‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    change ‖(lawAveragingOperator s f).compContinuous p‖ ≤ 1 * ‖f‖
    simpa using ((lawAveragingOperator s f).norm_compContinuous_le p).trans (lawAverage_norm_le s f)
  · have h := (lawAveragingProjection p s).le_opNorm (1 : X →ᵇ ℝ)
    have h1 : lawAveragingProjection p s 1 = 1 := by
      change (lawAveragingOperator s 1).compContinuous p = 1
      rw [lawAveragingOperator_one, BoundedContinuousFunction.one_compContinuous]
    simpa [h1] using h
theorem lawAveraging_spec [Nonempty Y] (p : C(X, Y)) (hp : Function.Surjective p)
    (s : C(Y, ProbabilityMeasure X))
    (hs : ∀ y, probabilityPushforward p (s y) = diracProba y) : LawAveragingStatement p s := by
  letI : Nonempty X := hp.nonempty
  exact ⟨lawAveragingOperator s, lawAveragingProjection p s, fun _ _ ↦ rfl,
    lawAveragingOperator_positive s, lawAveragingOperator_one s, lawAverage_norm_le s,
    lawAveragingOperator_pullback p s hs, fun _ ↦ rfl,
    lawAveragingProjection_idempotent p s hs, lawAveragingProjection_range p s hs,
    lawAveragingProjection_norm p s⟩
end PaperN.PartI
