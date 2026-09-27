import PaperN.PartII.FiniteDimensionalApproximation
import PaperN.PartII.MinimizerContinuity

namespace PaperN.PartII
open Set Filter Topology
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (S : Submodule ℝ F) [FiniteDimensional ℝ S]

noncomputable def bestApproximation (x : F) : S := (exists_bestApproximation S x).choose

theorem bestApproximation_spec (x : F) (b : S) :
    ‖x - (bestApproximation S x : F)‖ ≤ ‖x - b‖ :=
  (exists_bestApproximation S x).choose_spec b

theorem bestApproximation_norm_le (x : F) : ‖bestApproximation S x‖ ≤ 2 * ‖x‖ := by
  have hm := bestApproximation_spec S x 0
  simp only [Submodule.coe_zero, sub_zero] at hm
  have ht := norm_sub_le x (x - (bestApproximation S x : F))
  rw [sub_sub_cancel] at ht
  change ‖(bestApproximation S x : F)‖ ≤ _
  linarith

theorem bestApproximation_tendsto [StrictConvexSpace ℝ F]
    {xs : ℕ → F} {x : F} (hx : Tendsto xs atTop (𝓝 x)) :
    Tendsto (fun n ↦ bestApproximation S (xs n)) atTop (𝓝 (bestApproximation S x)) := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto xs hx).exists_norm_le
  have hb : Bornology.IsBounded (range (fun n ↦ bestApproximation S (xs n))) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨2 * C, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (bestApproximation_norm_le S (xs n)).trans (by linarith [hC (xs n) (mem_range_self n)])
  have hK := hb.isCompact_closure
  apply hK.tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall fun n ↦ subset_closure (mem_range_self n))
  intro a _ hcluster
  obtain ⟨φ, hφ, hlim⟩ := hcluster.tendsto_subseq
  apply bestApproximation_unique S x a (bestApproximation S x)
  · intro b
    have hx' := hx.comp hφ.tendsto_atTop
    have ha' := S.subtypeL.continuous.continuousAt.tendsto.comp hlim
    exact le_of_tendsto_of_tendsto (hx'.sub ha').norm
      (hx'.sub tendsto_const_nhds).norm
      (Eventually.of_forall fun n ↦ bestApproximation_spec S (xs (φ n)) b)
  · exact bestApproximation_spec S x

theorem continuous_bestApproximation [StrictConvexSpace ℝ F] :
    Continuous (bestApproximation S) := by
  apply continuous_iff_seqContinuous.mpr
  intro xs x hx
  exact bestApproximation_tendsto S hx

end PaperN.PartII

namespace PaperN.PartII
open MeasureTheory
variable {X ι : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Fintype ι]
  (μ : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
  (p : ENNReal) [Fact (1 ≤ p)] [StrictConvexSpace ℝ (Lp ℝ p μ)]

theorem continuous_coordinateLpMinimizer (v : ι → C(X, ℝ)) (hv : LinearIndependent ℝ v) :
    Continuous (coordinateLpMinimizer μ p v) := by
  let T := coordinateLpMap μ p v
  have hi : Function.Injective T :=
    (ContinuousMap.toLp_injective μ).comp (coordinateSynthesis_injective v hv)
  let e := LinearEquiv.ofInjective T hi
  have he : Continuous (fun f : Lp ℝ p μ ↦ e.symm (bestApproximation T.range f)) :=
    e.symm.toLinearMap.continuous_of_finiteDimensional.comp (continuous_bestApproximation T.range)
  have heq : coordinateLpMinimizer μ p v =
      (fun f : Lp ℝ p μ ↦ e.symm (bestApproximation T.range f)) := by
    funext f
    apply coordinateLp_minimizer_unique μ p v hv f
    · exact coordinateLpMinimizer_spec μ p v f
    · intro c
      have h := bestApproximation_spec T.range f ⟨T c, ⟨c, rfl⟩⟩
      have hh : T (e.symm (bestApproximation T.range f)) =
          (bestApproximation T.range f : Lp ℝ p μ) :=
        congrArg Subtype.val (e.apply_symm_apply _)
      change ‖f - T _‖ ≤ ‖f - T c‖
      rw [hh]
      exact h
  rw [heq]
  exact he

end PaperN.PartII

namespace PaperN.PartII
open MeasureTheory
variable {X ι : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Fintype ι]
  (μ : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
  (p : ENNReal) [Fact (1 ≤ p)] [StrictConvexSpace ℝ (Lp ℝ p μ)]

/-- Continuous coordinates of best approximations to distance profiles. -/
noncomputable def bestApproximationCoordinates (v : ι → C(X, ℝ)) (hv : LinearIndependent ℝ v) :
    C(X, EuclideanSpace ℝ ι) where
  toFun x := coordinateLpMinimizer μ p v (ContinuousMap.toLp p μ ℝ (distanceProfile x))
  continuous_toFun := by
    have hd : LipschitzWith 1 (distanceProfile (X := X)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using distanceProfile_sub_norm_le x y
    exact (continuous_coordinateLpMinimizer μ p v hv).comp
      ((ContinuousMap.toLp p μ ℝ).continuous.comp hd.continuous)

end PaperN.PartII
