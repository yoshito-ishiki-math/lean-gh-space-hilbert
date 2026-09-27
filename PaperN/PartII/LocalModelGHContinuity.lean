import PaperN.PartII.LocalModelGHMap
import PaperN.PartII.CoordinateBoundConvergence
import PaperN.PartII.CommonCorrespondences

namespace PaperN.PartII
open PaperN.Shared PaperN.PartI GromovHausdorff Filter
open scoped Topology

/-- Convergent coordinate pairs induce convergent compact pseudometric quotients. -/
theorem coordinate_gh_tendsto
    {X : Type*} (Xs : ℕ → Type*) [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    [∀ k, TopologicalSpace (Xs k)] [∀ k, CompactSpace (Xs k)] [∀ k, Nonempty (Xs k)]
    (n : ℕ) [NeZero n] (R : ∀ k, Correspondence (Xs k) X)
    (as : ∀ k, NormedCoordinatePair (Xs k) (EuclideanSpace ℝ (Fin n)))
    (a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin n)))
    (hn : Tendsto (fun k ↦ unitNormError (as k).norm a.norm) atTop (𝓝 0))
    (hc : Tendsto (fun k ↦ coordinateError (R k) (as k).coordinates a.coordinates) atTop (𝓝 0)) :
    Tendsto (fun k ↦ (as k).pseudometric.gh) atTop (𝓝 a.pseudometric.gh) := by
  let M := 1 + coordinateBound a.coordinates
  have hM := coordinateBound_eventually_le_of_error_tendsto Xs R
    (fun k ↦ (as k).coordinates) a.coordinates hc
  have ht : Tendsto (fun k ↦ 2 * M * unitNormError (as k).norm a.norm +
      2 * unitNormBound a.norm * coordinateError (R k) (as k).coordinates a.coordinates)
      atTop (𝓝 0) := by
    simpa using (hn.const_mul (2 * M)).add (hc.const_mul (2 * unitNormBound a.norm))
  have he : Tendsto (fun k ↦ correspondenceError (R k) (as k).pseudometric a.pseudometric)
      atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall (fun k ↦ error_nonneg (R k) _ _)) ?_ ht
    filter_upwards [hM] with k hk
    have he := coordinate_pseudometric_estimate n (R k) (as k).norm a.norm
      (as k).coordinates a.coordinates
    refine he.trans (add_le_add ?_ le_rfl)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by norm_num))
      (Real.iSup_nonneg (fun _ ↦ abs_nonneg _))
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ ↦ dist_nonneg)
    (fun k ↦ quotient_ghDist_le (R k) (as k).pseudometric a.pseudometric)
    (by simpa using he.div_const 2)

/-- A4 implies continuity of the quotient map on the whole local-model domain. -/
theorem LocalModel.continuous_ghMap {X₀ : MeasuredCompact.{0}} {τ : ℝ}
    (M : LocalModel X₀ τ) (hg : GHCommonEmbeddingInput.{0}) : Continuous M.ghMap := by
  letI : NeZero M.dimension := ⟨Nat.ne_of_gt M.dimension_pos⟩
  apply continuous_iff_seqContinuous.mpr
  intro qs q hq
  let Xs := fun k ↦ ghRepresentative (qs k).val
  let X := ghRepresentative q.val
  have hXs k : toGHSpace (Xs k) ∈ M.domain := by
    simpa only [Xs, ghRepresentative_class] using (qs k).property
  have hX : toGHSpace X ∈ M.domain := by
    simpa only [X, ghRepresentative_class] using q.property
  have ht : Tendsto (fun k ↦ toGHSpace (Xs k)) atTop (𝓝 (toGHSpace X)) := by
    simpa only [Xs, X, ghRepresentative_class, Function.comp_def] using
      (continuous_subtype_val.tendsto q).comp hq
  obtain ⟨C, hH⟩ := hg Xs X ht
  obtain ⟨a, as, ha, has, hn, hc⟩ := M.representatives_converge Xs X hXs hX C hH
  obtain ⟨R, hdisp, _⟩ := C.exists_correspondences_tendsto hH
  have h := coordinate_gh_tendsto (fun k ↦ Xs k) M.dimension R as a hn (hc R hdisp)
  have he k := M.ghMap_eq (Xs k) (hXs k) (as k) (has k)
  have he0 := M.ghMap_eq X hX a ha
  simp only [Xs, X, ghRepresentative_class] at he he0
  simpa only [← he, ← he0, Function.comp_def] using h

namespace AmbientKernel
/-- Continuous local GH approximation at every small center and positive tolerance. -/
theorem exists_continuous_local_approximation
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm) (hg : GHCommonEmbeddingInput.{0})
    (hk : DistanceKernelSpectralInput.{0})

    (hf : CompactEigenvalueFinitenessInput.{0})

    (X : MeasuredCompact.{0}) (τ : ℝ) (hτ : 0 < τ) :
    ∃ M : LocalModel X τ, Continuous M.ghMap ∧
      ∀ q : M.domain, dist (M.ghMap q) q.val < τ / 2 := by
  obtain ⟨M, hM⟩ := exists_uniformly_approximating_localModel hm hp hs hg hk   hf   X τ hτ
  refine ⟨M, M.continuous_ghMap hg, fun q ↦ ?_⟩
  exact (M.ghMap_dist_le q).trans_lt (div_lt_div_of_pos_right (hM q.val q.property) (by norm_num))
end AmbientKernel

end PaperN.PartII
