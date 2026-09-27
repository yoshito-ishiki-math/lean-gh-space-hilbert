import PaperN.PartI.ProkhorovIsometry

namespace PaperN.PartI
open MeasureTheory Set Metric Filter
open scoped Topology

/-- Uniformly close measurable maps send a probability to close Prokhorov probabilities. -/
theorem levyProkhorovDist_map_le_of_dist_le
    {A Z : Type*} [MeasurableSpace A] [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (μ : Measure A) [IsProbabilityMeasure μ] (f g : A → Z)
    (hf : Measurable f) (hg : Measurable g) {δ : ℝ} (hδ : 0 ≤ δ)
    (hfg : ∀ a, dist (f a) (g a) ≤ δ) :
    levyProkhorovDist (Measure.map f μ) (Measure.map g μ) ≤ δ := by
  letI : IsProbabilityMeasure (Measure.map f μ) := Measure.isProbabilityMeasure_map hf.aemeasurable
  letI : IsProbabilityMeasure (Measure.map g μ) := Measure.isProbabilityMeasure_map hg.aemeasurable
  apply levyProkhorovDist_le_of_forall_le _ _ hδ
  intro ε B hε hB
  rw [Measure.map_apply hf hB, Measure.map_apply hg isOpen_thickening.measurableSet]
  apply (measure_mono ?_).trans (le_add_right le_rfl)
  intro a ha
  exact mem_thickening_iff.mpr ⟨f a, ha, by simpa only [dist_comm] using (hfg a).trans_lt hε⟩

/-- Vanishing uniform errors give the Prokhorov convergence needed in probability lifting. -/
theorem levyProkhorovDist_map_tendsto_of_dist_le
    {A Z : Type*} [MeasurableSpace A] [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (μ : Measure A) [IsProbabilityMeasure μ] (fs : ℕ → A → Z) (g : A → Z)
    (hfs : ∀ n, Measurable (fs n)) (hg : Measurable g)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hlim : Tendsto δ atTop (𝓝 0))
    (hfg : ∀ n a, dist (fs n a) (g a) ≤ δ n) :
    Tendsto (fun n ↦ levyProkhorovDist (Measure.map (fs n) μ) (Measure.map g μ))
      atTop (𝓝 0) := by
  apply squeeze_zero (fun n ↦ ENNReal.toReal_nonneg) _ hlim
  intro n
  exact levyProkhorovDist_map_le_of_dist_le μ (fs n) g (hfs n) hg (hδ n) (hfg n)
end PaperN.PartI
