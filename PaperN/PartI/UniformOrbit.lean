import PaperN.PartI.UniformOrbitStatements

namespace PaperN.PartI
open MeasureTheory Set Filter TopologicalSpace
open scoped Topology BoundedContinuousFunction
universe u
namespace CommonRealization
variable {Xs : ℕ → MeasuredCompact.{u}} {X : MeasuredCompact.{u}}

/-- The ambient integral equals the manuscript's integral on the original carrier. -/
theorem integral_orbitProbabilityAt (C : CommonRealization Xs X) (n : ℕ)
    (g : Xs n ≃ᵢ Xs n) (f : C →ᵇ ℝ) :
    (∫ z, f z ∂(C.orbitProbabilityAt n g : Measure C)) =
      ∫ x, f (C.seqMap n (g x)) ∂((Xs n).probability : Measure (Xs n)) := by
  exact integral_map ((C.seq_isometry n).continuous.comp g.continuous).measurable.aemeasurable
    f.continuous.aestronglyMeasurable

/-- An invariant limiting measure is unchanged by the limiting carrier isometry. -/
theorem limitActionProbability_eq (C : CommonRealization Xs X)
    (hi : ∀ g : X ≃ᵢ X, Measure.map g X.measure = X.measure) (g : X ≃ᵢ X) :
    C.limitActionProbability g = C.limitProbability := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (C.limitMap ∘ g) X.measure = Measure.map C.limitMap X.measure
  rw [← Measure.map_map C.limit_isometry.continuous.measurable g.continuous.measurable, hi g]

/-- Uniformity over all isometries of each varying carrier; no full-support assumption is needed. -/
theorem eventually_orbitError_lt (C : CommonRealization Xs X)
    (hH : C.HausdorffConverges) (hW : C.WeakConverges)
    (hi : ∀ g : X ≃ᵢ X, Measure.map g X.measure = X.measure)
    (f : C →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ g : Xs n ≃ᵢ Xs n, C.orbitError f n g < ε := by
  by_contra h
  have hfreq : ∃ᶠ n in atTop, ∃ g : Xs n ≃ᵢ Xs n, ε ≤ C.orbitError f n g := by
    simpa only [not_forall, not_lt] using (Filter.not_eventually.mp h)
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hfreq
  choose gs hgs using hbad
  let D := C.subsequence φ
  obtain ⟨ψ, g, _, hg⟩ := D.actionProbability_subsequence
    (hH.comp hφ.tendsto_atTop) (hW.comp hφ.tendsto_atTop) gs
  rw [D.limitActionProbability_eq hi g] at hg
  have hg' : Tendsto (fun j ↦ C.orbitProbabilityAt (φ (ψ j)) (gs (ψ j))) atTop
      (𝓝 C.limitProbability) := hg
  have hI := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hg' f
  have he' : Tendsto (fun j ↦ C.orbitError f (φ (ψ j)) (gs (ψ j))) atTop (𝓝 0) := by
    simpa only [orbitError, Real.dist_eq, Real.norm_eq_abs] using
      tendsto_iff_dist_tendsto_zero.mp hI
  have hz : ε ≤ 0 := ge_of_tendsto he' (Filter.Eventually.of_forall fun j ↦ hgs (ψ j))
  exact (not_le_of_gt hε) hz

/-- Equation `eq:uniform-orbit-measures`: the exact supremum over each full isometry group. -/
theorem uniformOrbitIntegrals_spec (C : CommonRealization Xs X) :
    C.UniformOrbitIntegralsStatement := by
  intro hH hW hi f
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [C.eventually_orbitError_lt hH hW hi f (half_pos hε)] with n hn
  have hb : BddAbove (range (C.orbitError f n)) := by
    refine ⟨ε / 2, ?_⟩
    rintro _ ⟨g, rfl⟩
    exact (hn g).le
  have hlo : 0 ≤ ⨆ g, C.orbitError f n g :=
    (norm_nonneg _).trans (le_ciSup hb (IsometryEquiv.refl (Xs n)))
  have hhi : (⨆ g, C.orbitError f n g) ≤ ε / 2 := ciSup_le fun g ↦ (hn g).le
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hlo] using hhi.trans_lt (half_lt_self hε)
end CommonRealization
end PaperN.PartI
