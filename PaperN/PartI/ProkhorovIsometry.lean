import PaperN.PartI.CommonAmbient
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace PaperN.PartI
open MeasureTheory Set Metric Filter TopologicalSpace
open scoped Topology
variable {X Z : Type*} [MetricSpace X] [MetricSpace Z]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Z] [BorelSpace Z]

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Z] [BorelSpace Z] in
lemma preimage_thickening_image_isometry (e : X → Z) (he : Isometry e) (r : ℝ) (A : Set X) :
    e ⁻¹' thickening r (e '' A) = thickening r A := by
  ext x
  simp only [mem_preimage, mem_thickening_iff, mem_image]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, hd⟩
    exact ⟨y, hy, by simpa only [he.dist_eq] using hd⟩
  · rintro ⟨y, hy, hd⟩
    exact ⟨e y, ⟨y, hy, rfl⟩, by simpa only [he.dist_eq] using hd⟩

/-- The Prokhorov distance is unchanged under an isometric embedding of a complete carrier. -/
theorem levyProkhorovEDist_map_isometry [CompleteSpace X]
    (e : X → Z) (he : Isometry e) (μ ν : Measure X) :
    levyProkhorovEDist (Measure.map e μ) (Measure.map e ν) = levyProkhorovEDist μ ν := by
  have hm := he.continuous.measurable
  have hemb := he.isClosedEmbedding.measurableEmbedding
  apply le_antisymm
  · apply levyProkhorovEDist_le_of_forall
    intro ε B hε _ hB
    have hsub : thickening ε.toReal (e ⁻¹' B) ⊆ e ⁻¹' thickening ε.toReal B := by
      intro x hx
      obtain ⟨y, hy, hd⟩ := mem_thickening_iff.mp hx
      exact mem_thickening_iff.mpr ⟨e y, hy, by simpa only [he.dist_eq] using hd⟩
    rw [Measure.map_apply hm hB, Measure.map_apply hm hB,
      Measure.map_apply hm isOpen_thickening.measurableSet,
      Measure.map_apply hm isOpen_thickening.measurableSet]
    exact ⟨(left_measure_le_of_levyProkhorovEDist_lt hε (hB.preimage hm)).trans
      (add_le_add (measure_mono hsub) le_rfl),
      (right_measure_le_of_levyProkhorovEDist_lt hε (hB.preimage hm)).trans
      (add_le_add (measure_mono hsub) le_rfl)⟩
  · apply levyProkhorovEDist_le_of_forall
    intro ε B hε _ hB
    have hBi : MeasurableSet (e '' B) := hemb.measurableSet_image.mpr hB
    have hl := left_measure_le_of_levyProkhorovEDist_lt hε hBi
    have hr := right_measure_le_of_levyProkhorovEDist_lt hε hBi
    rw [Measure.map_apply hm hBi, Measure.map_apply hm isOpen_thickening.measurableSet,
      Set.preimage_image_eq _ he.injective, preimage_thickening_image_isometry e he] at hl hr
    exact ⟨hl, hr⟩

theorem levyProkhorovDist_map_isometry [CompleteSpace X]
    (e : X → Z) (he : Isometry e) (μ ν : Measure X) :
    levyProkhorovDist (Measure.map e μ) (Measure.map e ν) = levyProkhorovDist μ ν := by
  simp only [levyProkhorovDist, levyProkhorovEDist_map_isometry e he]

/-- Joint weak convergence of two probabilities gives convergence of their Prokhorov distance. -/
theorem levyProkhorovDist_tendsto [SeparableSpace Z]
    {μs νs : ℕ → ProbabilityMeasure Z} {μ ν : ProbabilityMeasure Z}
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν)) :
    Tendsto (fun n ↦ levyProkhorovDist (μs n : Measure Z) (νs n : Measure Z)) atTop
      (𝓝 (levyProkhorovDist (μ : Measure Z) (ν : Measure Z))) := by
  exact (LevyProkhorov.continuous_ofMeasure_probabilityMeasure.continuousAt.tendsto.comp hμ).dist
    (LevyProkhorov.continuous_ofMeasure_probabilityMeasure.continuousAt.tendsto.comp hν)
end PaperN.PartI
