import PaperN.PartII.FeaturePseudometricError

namespace PaperN.PartII
open PaperN.Shared PaperN.PartI GromovHausdorff Filter
open scoped Topology

variable {A : ℕ → MeasuredCompact.{0}} {τ : ℕ → ℝ}
    (M : ∀ i, LocalModel (A i) (τ i)) (ρ : PartitionOfUnity ℕ GHSpace)

/-- Convergent representatives and vanishing original distortion give convergence
of the actual global uniform error. -/
theorem modelError_tendsto_of_representatives
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
      atTop (𝓝 0))
    (hd : Tendsto (fun k ↦ (R k).distortion) atTop (𝓝 0)) :
    Tendsto (fun k ↦ modelError M ρ (toGHSpace (Xs k))) atTop
      (𝓝 (modelError M ρ (toGHSpace X))) := by
  let w := fun k i ↦ ρ i (toGHSpace (Xs k))
  let v := fun i ↦ ρ i (toGHSpace X)
  let E := fun k i ↦ coordinateError (R k) (as k i).dualFeature (a i).dualFeature
  let B := fun i ↦ ‖(a i).dualFeature‖
  let r := fun k ↦ ∑ i ∈ J, (|w k i| * E k i + |w k i - v i| * B i)
  have hE (i) (hi : i ∈ J) : Tendsto (fun k ↦ E k i) atTop (𝓝 0) := by
    letI : NeZero (M i).dimension := ⟨Nat.ne_of_gt (M i).dimension_pos⟩
    exact dualFeature_error_tendsto (fun k ↦ Xs k) R (fun k ↦ as k i) (a i) (hn i hi) (hc i hi)
  have hw (i) : Tendsto (fun k ↦ w k i) atTop (𝓝 (v i)) :=
    (ρ i).continuous.continuousAt.tendsto.comp hq
  have hr : Tendsto r atTop (𝓝 0) := by
    have h : Tendsto r atTop (𝓝 (∑ i ∈ J, (|v i| * 0 + |v i - v i| * B i))) := by
      apply tendsto_finsetSum
      intro i hi
      exact ((hw i).abs.mul (hE i hi)).add (((hw i).sub tendsto_const_nhds).abs.mul_const (B i))
    simpa using h
  let f := fun k (x : Xs k) ↦ finiteBlockFeature J (w k) (fun i ↦ (as k i).dualFeature x)
  let g := fun (x : X) ↦ finiteBlockFeature J v (fun i ↦ (a i).dualFeature x)
  have hb (k) (z : (R k).rel) : dist (f k z.val.1) (g z.val.2) ≤ r k := by
    apply (finiteBlockFeature_dist_le_variable J (w k) v _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [dist_eq_norm] using coordinateError_apply_le (R k) (as k i).dualFeature (a i).dualFeature z
    · exact mul_le_mul_of_nonneg_left ((a i).dualFeature.norm_coe_le_norm _) (abs_nonneg _)
  have h := feature_uniform_error_tendsto (fun k ↦ Xs k) R
    (fun k ↦ modelPseudometric M ρ (Xs k)) (modelPseudometric M ρ X) f g
    (fun k ↦ modelPseudometric_eq_representative_feature M ρ hρ (Xs k) J (hJs k) (as k) (has k))
    (modelPseudometric_eq_representative_feature M ρ hρ X J hJ a ha) r hb hr hd
  simpa only [modelError_eq M ρ hρ, modelUniformError] using h

/-- Local-model convergence supplies all representatives on a common finite family
whose domains contain the whole sequence. -/
theorem modelError_tendsto_on_common_domains
    (hρ : ρ.IsSubordinate (fun i ↦ (M i).domain)) (hg : GHCommonEmbeddingInput.{0})
    (Xs : ℕ → MeasuredCompact.{0}) (X : MeasuredCompact.{0})
    (hq : Tendsto (fun k ↦ toGHSpace (Xs k)) atTop (𝓝 (toGHSpace X)))
    (J : Finset ℕ) (hJs : ∀ k, ρ.finsupport (toGHSpace (Xs k)) ⊆ J)
    (hJ : ρ.finsupport (toGHSpace X) ⊆ J)
    (hDs : ∀ k i, i ∈ J → toGHSpace (Xs k) ∈ (M i).domain)
    (hD : ∀ i, i ∈ J → toGHSpace X ∈ (M i).domain) :
    Tendsto (fun k ↦ modelError M ρ (toGHSpace (Xs k))) atTop
      (𝓝 (modelError M ρ (toGHSpace X))) := by
  classical
  obtain ⟨C, hH⟩ := hg Xs X hq
  obtain ⟨R, hdisp, hdist⟩ := C.exists_correspondences_tendsto hH
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
  exact modelError_tendsto_of_representatives M ρ hρ Xs X hq J hJs hJ R
    (fun k i ↦ as i k) a
    (fun k i hi ↦ (hh i (hJs k hi)).2.1 k)
    (fun i hi ↦ (hh i (hJ hi)).1)
    (fun i hi ↦ (hh i hi).2.2.1) (fun i hi ↦ (hh i hi).2.2.2) hdist

/-- The global uniform pseudometric error is continuous. The only additional input is the
registered common-embedding theorem for convergent GH sequences. -/
theorem continuous_modelError
    (hρ : ρ.IsSubordinate (fun i ↦ (M i).domain)) (hg : GHCommonEmbeddingInput.{0}) :
    Continuous (modelError M ρ) := by
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
  have h := modelError_tendsto_on_common_domains M ρ hρ hg Xs X ht J
    (fun k ↦ hsupp _ (hXs k)) (hsupp _ hX)
    (fun k i hi ↦ hdom _ (hXs k) i hi) (fun i hi ↦ hdom _ hX i hi)
  apply (tendsto_add_atTop_iff_nat N).mp
  simpa only [Xs, X, ghRepresentative_class, Function.comp_def] using h

end PaperN.PartII
