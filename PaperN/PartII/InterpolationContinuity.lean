import PaperN.PartII.ModelInterpolation

namespace PaperN.PartII
open PaperN.Shared PaperN.PartI GromovHausdorff Filter
open scoped Topology

variable {A : ℕ → MeasuredCompact.{0}} {τ : ℕ → ℝ}
    (M : ∀ i, LocalModel (A i) (τ i)) (ρ : PartitionOfUnity ℕ GHSpace) (t : Set.Icc (0 : ℝ) 1)

/-- Convergent representatives and vanishing original distortion give convergence
of the quotient interpolation at a fixed time. -/
theorem modelInterpolation_tendsto_of_representatives
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
    Tendsto (fun k ↦ modelInterpolation M ρ (toGHSpace (Xs k)) t) atTop
      (𝓝 (modelInterpolation M ρ (toGHSpace X) t)) := by
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
  have he (k) : correspondenceError (R k) (modelPseudometric M ρ (Xs k))
      (modelPseudometric M ρ X) ≤ 2*r k :=
    feature_pseudometric_error_le (R k) _ _ (f k) g
      (modelPseudometric_eq_representative_feature M ρ hρ (Xs k) J (hJs k) (as k) (has k))
      (modelPseudometric_eq_representative_feature M ρ hρ X J hJ a ha) (r k) (hb k)
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hbound (k) : dist (modelInterpolation M ρ (toGHSpace (Xs k)) t)
      (modelInterpolation M ρ (toGHSpace X) t) ≤
        ((1-t.val)*(R k).distortion+t.val*(2*r k))/2 := by
    rw [modelInterpolation_eq M ρ hρ, modelInterpolation_eq M ρ hρ]
    apply (quotient_ghDist_le (R k) _ _).trans
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply (error_blend_le (R k) _ _ _ _ t).trans
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (he k) t.property.1)
  apply squeeze_zero (fun _ ↦ dist_nonneg) hbound
  simpa using ((hd.const_mul (1-t.val)).add ((hr.const_mul 2).const_mul t.val)).div_const 2

/-- Local-model convergence supplies all representatives on a common finite family
whose domains contain the whole sequence. -/
theorem modelInterpolation_tendsto_on_common_domains
    (hρ : ρ.IsSubordinate (fun i ↦ (M i).domain)) (hg : GHCommonEmbeddingInput.{0})
    (Xs : ℕ → MeasuredCompact.{0}) (X : MeasuredCompact.{0})
    (hq : Tendsto (fun k ↦ toGHSpace (Xs k)) atTop (𝓝 (toGHSpace X)))
    (J : Finset ℕ) (hJs : ∀ k, ρ.finsupport (toGHSpace (Xs k)) ⊆ J)
    (hJ : ρ.finsupport (toGHSpace X) ⊆ J)
    (hDs : ∀ k i, i ∈ J → toGHSpace (Xs k) ∈ (M i).domain)
    (hD : ∀ i, i ∈ J → toGHSpace X ∈ (M i).domain) :
    Tendsto (fun k ↦ modelInterpolation M ρ (toGHSpace (Xs k)) t) atTop
      (𝓝 (modelInterpolation M ρ (toGHSpace X) t)) := by
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
  exact modelInterpolation_tendsto_of_representatives M ρ t hρ Xs X hq J hJs hJ R
    (fun k i ↦ as i k) a
    (fun k i hi ↦ (hh i (hJs k hi)).2.1 k)
    (fun i hi ↦ (hh i (hJ hi)).1)
    (fun i hi ↦ (hh i hi).2.2.1) (fun i hi ↦ (hh i hi).2.2.2) hdist

/-- The quotient interpolation is continuous in the input at each fixed time. The only additional input is the
registered common-embedding theorem for convergent GH sequences. -/
theorem continuous_modelInterpolation_fixed
    (hρ : ρ.IsSubordinate (fun i ↦ (M i).domain)) (hg : GHCommonEmbeddingInput.{0}) :
    Continuous (fun q ↦ modelInterpolation M ρ q t) := by
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
  have h := modelInterpolation_tendsto_on_common_domains M ρ t hρ hg Xs X ht J
    (fun k ↦ hsupp _ (hXs k)) (hsupp _ hX)
    (fun k i hi ↦ hdom _ (hXs k) i hi) (fun i hi ↦ hdom _ hX i hi)
  apply (tendsto_add_atTop_iff_nat N).mp
  simpa only [Xs, X, ghRepresentative_class, Function.comp_def] using h

/-- The interpolation is jointly continuous in the GH input and closed-interval time. -/
theorem continuous_modelInterpolation
    (hρ : ρ.IsSubordinate (fun i ↦ (M i).domain)) (hg : GHCommonEmbeddingInput.{0}) :
    Continuous (fun p : GHSpace × Set.Icc (0 : ℝ) 1 ↦ modelInterpolation M ρ p.1 p.2) := by
  apply continuous_iff_seqContinuous.mpr
  intro ps p hp
  have hq := (continuous_fst.tendsto p).comp hp
  have ht : Tendsto (fun k ↦ (ps k).2.val) atTop (𝓝 p.2.val) :=
    (continuous_subtype_val.tendsto p.2).comp ((continuous_snd.tendsto p).comp hp)
  have hs := ((continuous_modelInterpolation_fixed M ρ p.2 hρ hg).tendsto p.1).comp hq
  have he := ((continuous_modelError M ρ hρ hg).tendsto p.1).comp hq
  have htime : Tendsto (fun k ↦ |(ps k).2.val-p.2.val| * modelError M ρ (ps k).1 / 2)
      atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, zero_mul, zero_div, Function.comp_def] using
      (((ht.sub (tendsto_const_nhds (x := p.2.val))).abs.mul he).div_const 2)
  have hspace := tendsto_iff_dist_tendsto_zero.mp hs
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ dist_nonneg)
    (fun k ↦ (dist_triangle (modelInterpolation M ρ (ps k).1 (ps k).2)
      (modelInterpolation M ρ (ps k).1 p.2) (modelInterpolation M ρ p.1 p.2)).trans
      (add_le_add (modelInterpolation_track_le M ρ (ps k).1 (ps k).2 p.2) le_rfl))
  simpa only [zero_add, Function.comp_def] using htime.add hspace

end PaperN.PartII
