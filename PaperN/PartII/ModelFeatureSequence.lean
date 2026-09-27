import PaperN.PartII.DualFeatureError

namespace PaperN.PartII
open PaperN.Shared PaperN.PartI GromovHausdorff Filter
open scoped Topology

/-- Finite families of converging coordinate pairs give convergent sphere-feature images. -/
theorem finiteDualFeatureImage_tendsto
    {X : Type*} (Xs : ℕ → Type*) [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    [∀ k, TopologicalSpace (Xs k)] [∀ k, CompactSpace (Xs k)] [∀ k, Nonempty (Xs k)]
    (n : ℕ → ℕ) (s : Finset ℕ) (hnpos : ∀ i ∈ s, 0 < n i)
    (R : ∀ k, Correspondence (Xs k) X)
    (as : ∀ k i, NormedCoordinatePair (Xs k) (EuclideanSpace ℝ (Fin (n i))))
    (a : ∀ i, NormedCoordinatePair X (EuclideanSpace ℝ (Fin (n i))))
    (w : ℕ → ℕ → ℝ) (v : ℕ → ℝ)
    (hw : ∀ i ∈ s, Tendsto (fun k ↦ w k i) atTop (𝓝 (v i)))
    (hn : ∀ i ∈ s, Tendsto (fun k ↦ unitNormError (as k i).norm (a i).norm) atTop (𝓝 0))
    (hc : ∀ i ∈ s, Tendsto (fun k ↦ coordinateError (R k) (as k i).coordinates (a i).coordinates)
      atTop (𝓝 0)) :
    Tendsto (fun k ↦ finiteFeatureImage s (w k) (fun i ↦ (as k i).dualFeature)
      (fun i _ ↦ (as k i).dualFeature.continuous)) atTop
      (𝓝 (finiteFeatureImage s v (fun i ↦ (a i).dualFeature)
        (fun i _ ↦ (a i).dualFeature.continuous))) := by
  apply finiteFeatureImage_tendsto Xs s w v _ _ _ _ R
    (fun k i ↦ coordinateError (R k) (as k i).dualFeature (a i).dualFeature)
    (fun i ↦ ‖(a i).dualFeature‖)
  · intro k i _ z
    simpa only [dist_eq_norm] using coordinateError_apply_le (R k) (as k i).dualFeature (a i).dualFeature z
  · intro i _ y
    exact (a i).dualFeature.norm_coe_le_norm y
  · exact hw
  · intro i hi
    letI : NeZero (n i) := ⟨Nat.ne_of_gt (hnpos i hi)⟩
    exact dualFeature_error_tendsto Xs R (fun k ↦ as k i) (a i) (hn i hi) (hc i hi)

variable {A : ℕ → MeasuredCompact.{0}} {τ : ℕ → ℝ}
    (M : ∀ i, LocalModel (A i) (τ i)) (ρ : PartitionOfUnity ℕ GHSpace)

/-- With a common active finite set and convergent local representatives, the global
orbit-valued candidate converges. -/
theorem modelApproximation_tendsto_of_representatives
    (hρ : ρ.IsSubordinate (fun i ↦ (M i).domain))
    (Xs : ℕ → MeasuredCompact.{0}) (X : MeasuredCompact.{0})
    (hq : Tendsto (fun k ↦ toGHSpace (Xs k)) atTop (𝓝 (toGHSpace X)))
    (J : Finset ℕ) (hJs : ∀ k, ρ.finsupport (toGHSpace (Xs k)) ⊆ J)
    (hJ : ρ.finsupport (toGHSpace X) ⊆ J)
    (R : ∀ k, Correspondence (Xs k) X)
    (as : ∀ k i, NormedCoordinatePair (Xs k) (EuclideanSpace ℝ (Fin (M i).dimension)))
    (a : ∀ i, NormedCoordinatePair X (EuclideanSpace ℝ (Fin (M i).dimension)))
    (has : ∀ k i (hi : i ∈ ρ.finsupport (toGHSpace (Xs k))),
      Quotient.mk _ (as k i) = (M i).coordinateClass (Xs k) (modelFeature_active_mem M ρ hρ (Xs k) i hi))
    (ha : ∀ i (hi : i ∈ ρ.finsupport (toGHSpace X)),
      Quotient.mk _ (a i) = (M i).coordinateClass X (modelFeature_active_mem M ρ hρ X i hi))
    (hn : ∀ i ∈ J, Tendsto (fun k ↦ unitNormError (as k i).norm (a i).norm) atTop (𝓝 0))
    (hc : ∀ i ∈ J, Tendsto (fun k ↦ coordinateError (R k) (as k i).coordinates (a i).coordinates)
      atTop (𝓝 0)) :
    Tendsto (fun k ↦ modelApproximation M ρ (toGHSpace (Xs k))) atTop
      (𝓝 (modelApproximation M ρ (toGHSpace X))) := by
  have h := finiteDualFeatureImage_tendsto (fun k ↦ Xs k) (fun i ↦ (M i).dimension) J
    (fun i _ ↦ (M i).dimension_pos) R as a
    (fun k i ↦ ρ i (toGHSpace (Xs k))) (fun i ↦ ρ i (toGHSpace X))
    (fun i _ ↦ (ρ i).continuous.continuousAt.tendsto.comp hq) hn hc
  have hp := ((SphereOrbit.projection_lipschitz (fun i ↦ (M i).dimension)).continuous.continuousAt.tendsto).comp h
  have he k := modelApproximation_eq_representatives_on_superset M ρ hρ (Xs k) J (hJs k) (as k) (has k)
  have he0 := modelApproximation_eq_representatives_on_superset M ρ hρ X J hJ a ha
  simpa only [Function.comp_def, ← he, ← he0] using hp

/-- Local-model convergence supplies all representatives on a common finite family
whose domains contain the whole sequence. -/
theorem modelApproximation_tendsto_on_common_domains
    (hρ : ρ.IsSubordinate (fun i ↦ (M i).domain)) (hg : GHCommonEmbeddingInput.{0})
    (Xs : ℕ → MeasuredCompact.{0}) (X : MeasuredCompact.{0})
    (hq : Tendsto (fun k ↦ toGHSpace (Xs k)) atTop (𝓝 (toGHSpace X)))
    (J : Finset ℕ) (hJs : ∀ k, ρ.finsupport (toGHSpace (Xs k)) ⊆ J)
    (hJ : ρ.finsupport (toGHSpace X) ⊆ J)
    (hDs : ∀ k i, i ∈ J → toGHSpace (Xs k) ∈ (M i).domain)
    (hD : ∀ i, i ∈ J → toGHSpace X ∈ (M i).domain) :
    Tendsto (fun k ↦ modelApproximation M ρ (toGHSpace (Xs k))) atTop
      (𝓝 (modelApproximation M ρ (toGHSpace X))) := by
  classical
  obtain ⟨C, hH⟩ := hg Xs X hq
  obtain ⟨R, hdisp, _⟩ := C.exists_correspondences_tendsto hH
  have hex : ∀ i, ∃ a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin (M i).dimension)),
      ∃ as : ∀ k, NormedCoordinatePair (Xs k) (EuclideanSpace ℝ (Fin (M i).dimension)),
      ∀ hi : i ∈ J,
        Quotient.mk _ a = (M i).coordinateClass X (hD i hi) ∧
        (∀ k, Quotient.mk _ (as k) = (M i).coordinateClass (Xs k) (hDs k i hi)) ∧
        Tendsto (fun k ↦ unitNormError (as k).norm a.norm) atTop (𝓝 0) ∧
        Tendsto (fun k ↦ coordinateError (R k) (as k).coordinates a.coordinates) atTop (𝓝 0) := by
    intro i
    by_cases hi : i ∈ J
    · obtain ⟨a, as, ha, has, hn, hc⟩ := (M i).representatives_converge Xs X
        (fun k ↦ hDs k i hi) (hD i hi) C hH
      exact ⟨a, as, fun _ ↦ ⟨ha, has, hn, hc R hdisp⟩⟩
    · exact ⟨(M i).chosenPair X, fun k ↦ (M i).chosenPair (Xs k), fun h ↦ (hi h).elim⟩
  choose a as hh using hex
  exact modelApproximation_tendsto_of_representatives M ρ hρ Xs X hq J hJs hJ R
    (fun k i ↦ as i k) a
    (fun k i hi ↦ (hh i (hJs k hi)).2.1 k)
    (fun i hi ↦ (hh i (hJ hi)).1)
    (fun i hi ↦ (hh i hi).2.2.1) (fun i hi ↦ (hh i hi).2.2.2)

/-- The assembled global orbit map is continuous. The only additional input is the
registered common-embedding theorem for convergent GH sequences. -/
theorem continuous_modelApproximation
    (hρ : ρ.IsSubordinate (fun i ↦ (M i).domain)) (hg : GHCommonEmbeddingInput.{0}) :
    Continuous (modelApproximation M ρ) := by
  apply continuous_iff_seqContinuous.mpr
  intro qs q hq
  obtain ⟨J, V, hV, hsub, hweights⟩ := partition_finite_common_neighborhood ρ
    (fun i ↦ (M i).domain) (fun i ↦ (M i).domain_open) hρ q
  have hqV : q ∈ V := mem_of_mem_nhds hV
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hq.eventually hV)
  let Xs := fun k ↦ ghRepresentative (qs (k + N))
  let X := ghRepresentative q
  have hXs k : toGHSpace (Xs k) ∈ V := by
    change toGHSpace (ghRepresentative (qs (k+N))) ∈ V
    rw [ghRepresentative_class]
    exact hN (k+N) (Nat.le_add_left N k)
  have hX : toGHSpace X ∈ V := by simpa only [X, ghRepresentative_class] using hqV
  have ht : Tendsto (fun k ↦ toGHSpace (Xs k)) atTop (𝓝 (toGHSpace X)) := by
    simpa only [Xs, X, ghRepresentative_class, Function.comp_def] using hq.comp (tendsto_add_atTop_nat N)
  have hsupp (r : GHSpace) (hr : r ∈ V) : ρ.finsupport r ⊆ J := by
    intro i hi
    exact (hweights r hr).1 ((ρ.mem_finsupport r).mp hi)
  have hdom (r : GHSpace) (hr : r ∈ V) (i : ℕ) (hi : i ∈ J) : r ∈ (M i).domain :=
    Set.mem_iInter.mp (Set.mem_iInter.mp (hsub hr) i) hi
  have h := modelApproximation_tendsto_on_common_domains M ρ hρ hg Xs X ht J
    (fun k ↦ hsupp _ (hXs k)) (hsupp _ hX)
    (fun k i hi ↦ hdom _ (hXs k) i hi) (fun i hi ↦ hdom _ hX i hi)
  apply (tendsto_add_atTop_iff_nat N).mp
  simpa only [Xs, X, ghRepresentative_class, Function.comp_def] using h

end PaperN.PartII
