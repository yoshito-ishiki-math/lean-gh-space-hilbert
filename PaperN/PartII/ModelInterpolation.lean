import PaperN.PartII.GlobalErrorContinuity

namespace PaperN.PartII
open PaperN.Shared PaperN.PartI GromovHausdorff

/-- The exact uniform change in a linearly interpolated pseudometric. -/
theorem blend_kernel_sub_norm {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (d e : ContinuousPseudometric X) (s t : Set.Icc (0 : ℝ) 1) :
    ‖(d.blend e s).kernel - (d.blend e t).kernel‖ =
      |s.val-t.val| * ‖d.kernel-e.kernel‖ := by
  have h : (d.blend e s).kernel - (d.blend e t).kernel =
      (s.val-t.val) • (e.kernel-d.kernel) := by
    apply ContinuousMap.ext
    intro z
    change ((1-s.val)*d z.1 z.2+s.val*e z.1 z.2) -
      ((1-t.val)*d z.1 z.2+t.val*e z.1 z.2) = (s.val-t.val)*(e z.1 z.2-d z.1 z.2)
    ring
  rw [h, norm_smul, Real.norm_eq_abs, norm_sub_rev]

/-- Passing interpolation to compact separated quotients has the half-error bound. -/
theorem blend_gh_dist_le {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (d e : ContinuousPseudometric X) (s t : Set.Icc (0 : ℝ) 1) :
    dist (d.blend e s).gh (d.blend e t).gh ≤ |s.val-t.val| * ‖d.kernel-e.kernel‖ / 2 := by
  have h := quotient_ghDist_le_norm (d.blend e s) (d.blend e t)
  rwa [blend_kernel_sub_norm] at h

/-- The quotient-valued interpolation underlying the global small homotopy. -/
noncomputable def modelInterpolation {A : ℕ → MeasuredCompact.{0}} {τ : ℕ → ℝ}
    (M : ∀ i, LocalModel (A i) (τ i)) (ρ : PartitionOfUnity ℕ GHSpace)
    (q : GHSpace) (t : Set.Icc (0 : ℝ) 1) : GHSpace :=
  ((ContinuousPseudometric.ofMetric (ghRepresentative q)).blend
    (modelPseudometric M ρ (ghRepresentative q)) t).gh

variable {A : ℕ → MeasuredCompact.{0}} {τ : ℕ → ℝ}
    (M : ∀ i, LocalModel (A i) (τ i)) (ρ : PartitionOfUnity ℕ GHSpace)

/-- Interpolation may be computed on any input carrier. -/
theorem modelInterpolation_eq (hρ : ρ.IsSubordinate (fun i ↦ (M i).domain))
    (X : MeasuredCompact.{0}) (t : Set.Icc (0 : ℝ) 1) :
    modelInterpolation M ρ (toGHSpace X) t =
      ((ContinuousPseudometric.ofMetric X).blend (modelPseudometric M ρ X) t).gh := by
  obtain ⟨e⟩ := toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp (ghRepresentative_class (toGHSpace X))
  apply pseudometric_gh_eq_of_equiv e.toEquiv
  intro x y
  change (1-t.val)*dist (e x) (e y)+t.val*modelPseudometric M ρ X (e x) (e y) = _
  rw [e.dist_eq, modelPseudometric_equivariant M ρ hρ _ X e]
  rfl

/-- The initial endpoint is the input GH class. -/
theorem modelInterpolation_zero (q : GHSpace) :
    modelInterpolation M ρ q ⟨0, by constructor <;> norm_num⟩ = q := by
  calc
    _ = (ContinuousPseudometric.ofMetric (ghRepresentative q)).gh := by
      apply pseudometric_gh_eq_of_equiv (Equiv.refl _)
      intro x y
      change dist x y = (1-(0:ℝ))*dist x y+0*modelPseudometric M ρ _ x y
      ring
    _ = q := by rw [ofMetric_gh, ghRepresentative_class]

/-- The final endpoint is realization of the global orbit map. -/
theorem modelInterpolation_one (q : GHSpace) :
    modelInterpolation M ρ q ⟨1, by constructor <;> norm_num⟩ =
      SphereOrbit.realization _ (modelApproximation M ρ q) := by
  change _ = (modelFeatureImage M ρ (ghRepresentative q)).toGHSpace
  rw [modelFeatureImage_gh_eq]
  apply pseudometric_gh_eq_of_equiv (Equiv.refl _)
  intro x y
  change modelPseudometric M ρ _ x y = (1-(1:ℝ))*dist x y+1*modelPseudometric M ρ _ x y
  ring

/-- Every time track obeys the exact uniform-error Lipschitz bound. -/
theorem modelInterpolation_track_le (q : GHSpace) (s t : Set.Icc (0 : ℝ) 1) :
    dist (modelInterpolation M ρ q s) (modelInterpolation M ρ q t) ≤
      |s.val-t.val| * modelError M ρ q / 2 :=
  blend_gh_dist_le _ _ s t

/-- Each individual interpolation track is Lipschitz, hence continuous in time. -/
theorem modelInterpolation_track_lipschitz (q : GHSpace) :
    LipschitzWith ⟨modelError M ρ q / 2,
      div_nonneg (modelError_nonneg M ρ q) (by norm_num)⟩ (modelInterpolation M ρ q) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  have h := modelInterpolation_track_le M ρ q s t
  change dist (modelInterpolation M ρ q s) (modelInterpolation M ρ q t) ≤
    (modelError M ρ q / 2) * |s.val-t.val|
  nlinarith

end PaperN.PartII
