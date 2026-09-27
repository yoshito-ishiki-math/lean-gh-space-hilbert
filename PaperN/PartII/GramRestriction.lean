import PaperN.PartII.GramNormalization
import PaperN.PartII.RealCutoffExtension

namespace PaperN.PartII
open MeasureTheory
open scoped RealInnerProductSpace
variable {X Z ι : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]

theorem continuousToL2_inner (μ : Measure X) [IsProbabilityMeasure μ] (f g : C(X, ℝ)) :
    ⟪continuousToL2 μ f, continuousToL2 μ g⟫ = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp μ (𝕜 := ℝ) (p := 2) f,
    ContinuousMap.coeFn_toLp μ (𝕜 := ℝ) (p := 2) g] with x hf hg
  simp only [continuousToL2] at *
  rw [hf, hg]
  simp [mul_comm]

omit [CompactSpace X] [CompactSpace Z] in
theorem continuousGram_map (e : C(X, Z)) (μ : ProbabilityMeasure X) (v : ι → C(Z, ℝ)) :
    continuousGram (μ.map e) v =
      continuousGram μ (fun i ↦ (v i).comp e) := by
  ext i j
  unfold continuousGram
  rw [ProbabilityMeasure.toMeasure_map]
  exact integral_map e.continuous.measurable.aemeasurable
    (show Continuous (fun z ↦ v i z * v j z) by fun_prop).aestronglyMeasurable

theorem continuousGram_eq_one_iff [DecidableEq ι] (μ : ProbabilityMeasure X) (v : ι → C(X, ℝ)) :
    continuousGram μ v = 1 ↔ Orthonormal ℝ (fun i ↦ continuousToL2 (μ : Measure X) (v i)) := by
  rw [orthonormal_iff_ite]
  simp only [continuousToL2_inner]
  constructor
  · intro h i j
    exact congrFun (congrFun h i) j
  · intro h
    ext i j
    exact h i j

omit [CompactSpace Z] in
theorem continuousGram_map_eq_one [DecidableEq ι] (e : C(X, Z)) (μ : ProbabilityMeasure X)
    (g : ι → C(Z, ℝ)) (v : ι → C(X, ℝ)) (hext : ∀ i, (g i).comp e = v i)
    (hv : Orthonormal ℝ (fun i ↦ continuousToL2 (μ : Measure X) (v i))) :
    continuousGram (μ.map e) g = 1 := by
  rw [continuousGram_map]
  simp_rw [hext]
  exact (continuousGram_eq_one_iff μ v).mpr hv

theorem normalized_restrictions_orthonormal [Fintype ι] [DecidableEq ι]
    (e : C(X, Z)) (μ : ProbabilityMeasure X) (g : ι → C(Z, ℝ))
    (hG : (continuousGram (μ.map e) g).PosDef) :
    Orthonormal ℝ (fun i ↦ continuousToL2 (μ : Measure X)
      ((normalizeContinuousFamily (μ.map e) g i).comp e)) := by
  apply (continuousGram_eq_one_iff μ _).mp
  rw [← continuousGram_map]
  exact normalizeContinuousFamily_gram _ g hG

theorem orthonormal_continuousFamily_span [Fintype ι]
    (μ : Measure X) [IsProbabilityMeasure μ] (S : Submodule ℝ C(X, ℝ)) [FiniteDimensional ℝ S]
    (v : ι → S) (hv : Orthonormal ℝ (fun i ↦ continuousToL2 μ (v i)))
    (hd : Fintype.card ι = Module.finrank ℝ S) :
    Submodule.span ℝ (Set.range v) = ⊤ := by
  have hi : LinearIndependent ℝ v :=
    LinearIndependent.of_comp ((continuousToL2 μ).toLinearMap.comp S.subtype) hv.linearIndependent
  exact hi.span_eq_top_of_card_eq_finrank' hd

end PaperN.PartII
