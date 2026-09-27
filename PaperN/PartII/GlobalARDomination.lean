import PaperN.PartII.GlobalOrbitApproximation
import PaperN.PartII.InterpolationCompatibility
import PaperN.PartII.SphereOrbitAR

namespace PaperN.PartII
open PaperN.PartI GromovHausdorff TopologicalSpace

/-- Every pair of points on a homotopy track is closer than half the prescribed error. -/
theorem modelInterpolation_track_lt
    {A : ℕ → MeasuredCompact.{0}} {τ : ℕ → ℝ}
    (M : ∀ i, LocalModel (A i) (τ i)) (ρ : PartitionOfUnity ℕ GHSpace)
    (hρ : ρ.IsSubordinate (fun i ↦ (M i).domain))
    (ε : GHSpace → ℝ) (he : ∀ i q, q ∈ (M i).domain → (M i).error q < ε q)
    (q : GHSpace) (s t : Set.Icc (0 : ℝ) 1) :
    dist (modelInterpolation M ρ q s) (modelInterpolation M ρ q t) < ε q / 2 := by
  have htime : |s.val - t.val| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [s.property.1, s.property.2, t.property.1, t.property.2]
  have he0 := modelError_nonneg M ρ q
  have he1 := modelError_lt M ρ hρ ε he q
  have hmul := mul_le_mul_of_nonneg_right htime he0
  have hd := modelInterpolation_track_le M ρ q s t
  linarith

/-- A uniform bound for the diameter of an entire interpolation track. -/
theorem modelInterpolation_track_diam_le
    {A : ℕ → MeasuredCompact.{0}} {τ : ℕ → ℝ}
    (M : ∀ i, LocalModel (A i) (τ i)) (ρ : PartitionOfUnity ℕ GHSpace) (q : GHSpace) :
    Metric.diam (Set.range (modelInterpolation M ρ q)) ≤ modelError M ρ q / 2 := by
  apply Metric.diam_le_of_forall_dist_le (div_nonneg (modelError_nonneg M ρ q) (by norm_num))
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
  have htime : |s.val - t.val| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [s.property.1, s.property.2, t.property.1, t.property.2]
  have hmul := mul_le_mul_of_nonneg_right htime (modelError_nonneg M ρ q)
  have hd := modelInterpolation_track_le M ρ q s t
  linarith

namespace AmbientKernel
/-- Global small homotopy domination through a concrete separable metrizable AR.
The AR conclusion retains the two general literature inputs; all maps and
homotopy properties are constructed by the preceding modules. -/
theorem exists_AR_domination
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm) (hg : GHCommonEmbeddingInput.{0})
    (hk : DistanceKernelSpectralInput.{0})

    (hf : CompactEigenvalueFinitenessInput.{0})

    (hH : EquivariantHyperspaceARInput) (hO : OrbitARInput)
    (ε : GHSpace → ℝ) (hε : Continuous ε) (hpos : ∀ q, 0 < ε q) :
    ∃ n : ℕ → ℕ, (∀ i, 0 < n i) ∧
      SeparableSpace (SphereOrbit.Space n) ∧ IsAbsoluteRetract.{0,0} (SphereOrbit.Space n) ∧
      ∃ f : GHSpace → SphereOrbit.Space n,
        Continuous f ∧ Continuous (SphereOrbit.realization n) ∧
        ∃ e : GHSpace → ℝ, Continuous e ∧ (∀ q, 0 ≤ e q) ∧ (∀ q, e q < ε q) ∧
        ∃ H : GHSpace → Set.Icc (0 : ℝ) 1 → GHSpace,
          Continuous (fun p : GHSpace × Set.Icc (0 : ℝ) 1 ↦ H p.1 p.2) ∧
          (∀ q, H q ⟨0, by constructor <;> norm_num⟩ = q) ∧
          (∀ q, H q ⟨1, by constructor <;> norm_num⟩ = SphereOrbit.realization n (f q)) ∧
          (∀ q s t, dist (H q s) (H q t) ≤ |s.val - t.val| * e q / 2) ∧
          (∀ q s t, dist (H q s) (H q t) < ε q / 2) ∧
          (∀ q, Metric.diam (Set.range (H q)) < ε q) := by
  obtain ⟨a, M, ρ, hρ, _, he⟩ :=
    exists_localModel_partition hm hp hs hg hk   hf   ε hε hpos
  refine ⟨fun i ↦ (M i).dimension, fun i ↦ (M i).dimension_pos,
    SphereOrbit.separableSpace _, SphereOrbit.absoluteRetract _ hH hO,
    modelApproximation M ρ, continuous_modelApproximation M ρ hρ hg,
    (SphereOrbit.realization_lipschitz _).continuous,
    modelError M ρ, continuous_modelError M ρ hρ hg, modelError_nonneg M ρ,
    modelError_lt M ρ hρ ε he,
    modelInterpolation M ρ, continuous_modelInterpolation M ρ hρ hg,
    modelInterpolation_zero M ρ, modelInterpolation_one M ρ,
    modelInterpolation_track_le M ρ, modelInterpolation_track_lt M ρ hρ ε he, ?_⟩
  intro q
  have hd := modelInterpolation_track_diam_le M ρ q
  have he1 := modelError_lt M ρ hρ ε he q
  have hp0 := hpos q
  linarith

end AmbientKernel
end PaperN.PartII
