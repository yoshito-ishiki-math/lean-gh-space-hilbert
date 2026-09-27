import PaperN.PartII.SubspaceClassMembership
import PaperN.PartII.ModelSupConvergence

namespace PaperN.PartII
open MeasureTheory Filter Topology PaperN.Shared

/-- Full representatives can be chosen before all correspondences, with both
model suprema converging, from convergent ambient orthonormal families. -/
theorem exists_convergent_subspace_representatives
    {Z X : Type*} (Xs : ℕ → Type*)
    [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [∀ k, MetricSpace (Xs k)] [∀ k, CompactSpace (Xs k)] [∀ k, Nonempty (Xs k)]
    [∀ k, MeasurableSpace (Xs k)] [∀ k, BorelSpace (Xs k)]
    (μs : ∀ k, ProbabilityMeasure (Xs k)) (μ : ProbabilityMeasure X)
    [∀ k, (μs k : Measure (Xs k)).IsOpenPosMeasure] [(μ : Measure X).IsOpenPosMeasure]
    (Ss : ∀ k, Submodule ℝ C(Xs k, ℝ)) (S : Submodule ℝ C(X, ℝ))
    [∀ k, FiniteDimensional ℝ (Ss k)] [FiniteDimensional ℝ S]
    (es : ∀ k, Xs k → Z) (hes : ∀ k, Isometry (es k)) (e : X → Z) (he : Isometry e)
    (hμ : Tendsto (fun k ↦ (μs k).map (hes k).continuous.measurable.aemeasurable)
      atTop (𝓝 (μ.map he.continuous.measurable.aemeasurable)))
    (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp2 : 2 ≤ p)
    [∀ k, StrictConvexSpace ℝ (Lp ℝ p (μs k : Measure (Xs k)))]
    [StrictConvexSpace ℝ (Lp ℝ p (μ : Measure X))]
    (n : ℕ) [NeZero n] (hds : ∀ k, n = Module.finrank ℝ (Ss k)) (hd : n = Module.finrank ℝ S)
    (vs : ℕ → Fin n → C(Z, ℝ)) (v : Fin n → C(Z, ℝ))
    (hv : ∀ i, Tendsto (fun k ↦ vs k i) atTop (𝓝 (v i)))
    (hmem : ∀ i, (v i).comp ⟨e, he.continuous⟩ ∈ S)
    (ho : Orthonormal ℝ (fun i ↦ continuousToL2 (μ : Measure X)
      ((v i).comp ⟨e, he.continuous⟩)))
    (hvs : ∀ᶠ k in atTop,
      (∀ i, (vs k i).comp ⟨es k, (hes k).continuous⟩ ∈ Ss k) ∧
      Orthonormal ℝ (fun i ↦ continuousToL2 (μs k : Measure (Xs k))
        ((vs k i).comp ⟨es k, (hes k).continuous⟩))) :
    ∃ a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin n)),
      ∃ as : ∀ k, NormedCoordinatePair (Xs k) (EuclideanSpace ℝ (Fin n)),
        Quotient.mk _ a = subspaceCoordinateClass (μ : Measure X) S p n hd ∧
        (∀ k, Quotient.mk _ (as k) = subspaceCoordinateClass (μs k : Measure (Xs k))
          (Ss k) p n (hds k)) ∧
        Tendsto (fun k ↦ unitNormError (as k).norm a.norm) atTop (𝓝 0) ∧
        ∀ R : ∀ k, Correspondence (Xs k) X,
          Tendsto (fun k ↦ ⨆ z : (R k).rel, dist (es k z.val.1) (e z.val.2)) atTop (𝓝 0) →
          Tendsto (fun k ↦ coordinateError (R k) (as k).coordinates a.coordinates) atTop (𝓝 0) := by
  let w := fun i ↦ (v i).comp ⟨e, he.continuous⟩
  let ws := fun k i ↦ (vs k i).comp ⟨es k, (hes k).continuous⟩
  obtain ⟨a, hac, haf, han⟩ := exists_subspace_class_representative
    (μ : Measure X) S p n hd w hmem ho
  obtain ⟨as, hasc, hase⟩ := repair_subspace_class_families Xs μs Ss p n hds ws hvs
  have hnorm : Tendsto (fun k ↦ unitNormError
      (coordinateLpNorm (μs k : Measure (Xs k)) p (ws k)) a.norm) atTop (𝓝 0) := by
    have h := coordinateLpNorm_unitNormError_tendsto _ _ hμ p hp vs v hv
    have heqs k b := coordinateLpNorm_map (μs k)
      (⟨es k, (hes k).continuous⟩ : C(Xs k, Z)) p hp (vs k) b
    have heq b := coordinateLpNorm_map μ (⟨e, he.continuous⟩ : C(X, Z)) p hp v b
    simpa only [unitNormError, heqs, heq, han] using h
  have hrepair := coordinate_class_repair_preserves_suprema Xs as _ _ hase a hnorm
  refine ⟨a, as, hac, hasc, hrepair.1, ?_⟩
  intro R hR
  apply hrepair.2 R
  have hi : LinearIndependent ℝ w :=
    LinearIndependent.of_comp (continuousToL2 (μ : Measure X)).toLinearMap ho.linearIndependent
  have ht := nearby_pair_sup_tendsto (fun k ↦ (R k).rel)
    (fun k z ↦ es k z.val.1) (fun _ z ↦ e z.val.2)
    (fun k z ↦ coordinateLpMinimizer (μs k : Measure (Xs k)) p (ws k)
      (ContinuousMap.toLp p (μs k : Measure (Xs k)) ℝ (distanceProfile z.val.1)))
    (fun _ z ↦ coordinateLpMinimizer (μ : Measure X) p w
      (ContinuousMap.toLp p (μ : Measure X) ℝ (distanceProfile z.val.2))) hR ?_
  · simpa only [dist_eq_norm, haf] using ht
  · intro r hr ε hε
    filter_upwards [embedded_coefficient_uniform_nearby Xs μs μ es hes e he hμ p hp
      vs v hv hi hp2 (hvs.mono (fun _ h ↦ h.2)) r hr ε hε] with k hk
    intro z hz
    exact hk z.val.1 z.val.2 hz

end PaperN.PartII
