import PaperN.PartII.FeatureImageConvergence
import PaperN.PartII.DualRepresentationContinuity

namespace PaperN.PartII
open PaperN.Shared Filter
open scoped Topology
variable {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    [NormedAddCommGroup E]

omit [Nonempty X] [Nonempty Y] in
theorem coordinateError_bddAbove (R : Correspondence X Y) (f : C(X,E)) (g : C(Y,E)) :
    BddAbove (Set.range (fun z : R.rel ↦ ‖f z.val.1 - g z.val.2‖)) := by
  refine ⟨‖f‖ + ‖g‖, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact (norm_sub_le _ _).trans (add_le_add (f.norm_coe_le_norm _) (g.norm_coe_le_norm _))

omit [Nonempty X] [Nonempty Y] in
theorem coordinateError_apply_le (R : Correspondence X Y) (f : C(X,E)) (g : C(Y,E))
    (z : R.rel) : ‖f z.val.1 - g z.val.2‖ ≤ coordinateError R f g :=
  le_ciSup (coordinateError_bddAbove R f g) z

omit [Nonempty Y] in
theorem coordinateError_nonneg (R : Correspondence X Y) (f : C(X,E)) (g : C(Y,E)) :
    0 ≤ coordinateError R f g :=
  (norm_nonneg _).trans (coordinateError_apply_le R f g (Classical.choice inferInstance))

section Inner
variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [Nonempty Y] in
/-- Relative norm control gives a uniform bound for the dual-feature error. -/
theorem dualFeature_error_le (R : Correspondence X Y)
    (a : NormedCoordinatePair X E) (b : NormedCoordinatePair Y E)
    (δ L : ℝ) (hδ : 0 ≤ δ) (hsmall : δ < 1) (hL : 0 ≤ L)
    (hl : ∀ v, (1-δ) * b.norm v ≤ a.norm v)
    (hu : ∀ v, a.norm v ≤ (1+δ) * b.norm v)
    (hbound : ∀ v, b.norm v ≤ L * ‖v‖) :
    coordinateError R a.dualFeature b.dualFeature ≤
      (1+δ) * L * coordinateError R a.coordinates b.coordinates + δ * L * ‖b.coordinates‖ := by
  apply ciSup_le
  intro z
  change ‖coordinateDualEmbedding a.norm a.definite (a.coordinates z.val.1) -
    coordinateDualEmbedding b.norm b.definite (b.coordinates z.val.2)‖ ≤ _
  calc
    _ ≤ ‖coordinateDualEmbedding a.norm a.definite (a.coordinates z.val.1) -
        coordinateDualEmbedding a.norm a.definite (b.coordinates z.val.2)‖ +
        ‖coordinateDualEmbedding a.norm a.definite (b.coordinates z.val.2) -
        coordinateDualEmbedding b.norm b.definite (b.coordinates z.val.2)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (1+δ) * b.norm (a.coordinates z.val.1 - b.coordinates z.val.2) +
        δ * b.norm (b.coordinates z.val.2) := by
      rw [coordinateDualEmbedding_norm_sub]
      exact add_le_add (hu _) (coordinateDualEmbedding_sub_norm_le b.norm a.norm
        b.definite a.definite δ hδ hsmall hl hu _)
    _ ≤ (1+δ) * (L * coordinateError R a.coordinates b.coordinates) +
        δ * (L * ‖b.coordinates‖) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left ((hbound _).trans
          (mul_le_mul_of_nonneg_left (coordinateError_apply_le R _ _ z) hL)) (by positivity)
      · exact mul_le_mul_of_nonneg_left ((hbound _).trans
          (mul_le_mul_of_nonneg_left (b.coordinates.norm_coe_le_norm _) hL)) hδ
    _ = _ := by ring

omit [Nonempty Y] in
/-- Local norm and coordinate convergence give uniform dual-feature convergence
along the same correspondences on varying carriers. -/
theorem dualFeature_error_tendsto [Nontrivial E]
    (Xs : ℕ → Type*) [∀ k, TopologicalSpace (Xs k)] [∀ k, CompactSpace (Xs k)]
    [∀ k, Nonempty (Xs k)] (R : ∀ k, Correspondence (Xs k) Y)
    (as : ∀ k, NormedCoordinatePair (Xs k) E) (a : NormedCoordinatePair Y E)
    (hn : Tendsto (fun k ↦ unitNormError (as k).norm a.norm) atTop (𝓝 0))
    (hc : Tendsto (fun k ↦ coordinateError (R k) (as k).coordinates a.coordinates) atTop (𝓝 0)) :
    Tendsto (fun k ↦ coordinateError (R k) (as k).dualFeature a.dualFeature) atTop (𝓝 0) := by
  obtain ⟨C, hC, hco⟩ := exists_norm_le_coordinateNorm a.norm a.definite
  let L := ‖(CoordinateNormCarrier.continuousLinearEquiv a.norm a.definite).toContinuousLinearMap‖
  have hL : 0 ≤ L := norm_nonneg _
  have hbound (v : E) : a.norm v ≤ L * ‖v‖ :=
    (CoordinateNormCarrier.continuousLinearEquiv a.norm a.definite).toContinuousLinearMap.le_opNorm v
  let S := Metric.sphere (0 : E) 1
  letI : Nonempty S := (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)).to_subtype
  have hb (k : ℕ) : BddAbove (Set.range (fun u : S ↦ |(as k).norm u - a.norm u|)) :=
    (isCompact_range (((seminorm_continuous_finiteDimensional (as k).norm).comp continuous_subtype_val).sub
      ((seminorm_continuous_finiteDimensional a.norm).comp continuous_subtype_val)).abs).bddAbove
  have hnonneg (k : ℕ) : 0 ≤ unitNormError (as k).norm a.norm :=
    (abs_nonneg _).trans (le_ciSup (hb k) (Classical.choice inferInstance))
  have ht : Tendsto (fun k ↦ unitNormError (as k).norm a.norm * C) atTop (𝓝 0) := by
    simpa using hn.mul_const C
  have hlim : Tendsto (fun k ↦
      (1 + unitNormError (as k).norm a.norm * C) * L *
        coordinateError (R k) (as k).coordinates a.coordinates +
      (unitNormError (as k).norm a.norm * C) * L * ‖a.coordinates‖) atTop (𝓝 0) := by
    convert (((tendsto_const_nhds.add ht).mul_const L).mul hc).add
      ((ht.mul_const L).mul_const ‖a.coordinates‖) using 1; simp
  apply squeeze_zero' (Eventually.of_forall fun k ↦ coordinateError_nonneg (R k) _ _) _ hlim
  filter_upwards [ht.eventually (gt_mem_nhds zero_lt_one)] with k hk
  obtain ⟨hl, hu⟩ := coordinateNorm_relative_of_sphere_error a.norm (as k).norm C
    (unitNormError (as k).norm a.norm) hC.le (hnonneg k) hco
    (fun v hv ↦ le_ciSup (hb k) ⟨v, mem_sphere_zero_iff_norm.mpr hv⟩)
  exact dualFeature_error_le (R k) (as k) a _ L (mul_nonneg (hnonneg k) hC.le) hk hL hl hu hbound

end Inner
end PaperN.PartII
