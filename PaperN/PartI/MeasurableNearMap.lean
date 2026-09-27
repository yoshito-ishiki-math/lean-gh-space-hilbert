import PaperN.PartI.ProkhorovMapApproximation

namespace PaperN.PartI
open MeasureTheory Set Metric TopologicalSpace

/-- Select nearby target points measurably by the first suitable point of a dense sequence. -/
theorem exists_measurable_near_map
    {A B Z : Type*} [MeasurableSpace A] [MetricSpace B] [SeparableSpace B] [Nonempty B]
    [MeasurableSpace B] [BorelSpace B] [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (f : A → Z) (hf : Measurable f) (g : B → Z) (hg : Continuous g) (r : ℝ)
    (h : ∀ a, ∃ b, dist (f a) (g b) < r) :
    ∃ s : A → B, Measurable s ∧ ∀ a, dist (f a) (g (s a)) < r := by
  classical
  have hn : ∀ a, ∃ n, dist (f a) (g (denseSeq B n)) < r := by
    intro a
    exact (denseRange_denseSeq B).exists_mem_open
      (isOpen_lt (continuous_const.dist hg) continuous_const) (h a)
  refine ⟨fun a ↦ denseSeq B (Nat.find (hn a)), ?_, fun a ↦ Nat.find_spec (hn a)⟩
  apply Measurable.find (fun _ ↦ measurable_const) _ hn
  intro n
  exact measurableSet_lt ((continuous_id.dist continuous_const).measurable.comp hf) measurable_const

/-- Hausdorff-close compact images admit a measurable transport with any strict error margin. -/
theorem exists_measurable_map_of_hausdorffDist_lt
    {A B Z : Type*} [MetricSpace A] [CompactSpace A] [Nonempty A]
    [MeasurableSpace A] [BorelSpace A] [MetricSpace B] [CompactSpace B] [Nonempty B]
    [MeasurableSpace B] [BorelSpace B] [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (f : A → Z) (hf : Continuous f) (g : B → Z) (hg : Continuous g) (r : ℝ)
    (hr : hausdorffDist (range f) (range g) < r) :
    ∃ s : A → B, Measurable s ∧ ∀ a, dist (f a) (g (s a)) < r := by
  apply exists_measurable_near_map f hf.measurable g hg r
  intro a
  have hfin := hausdorffEDist_ne_top_of_nonempty_of_bounded (range_nonempty f)
    (range_nonempty g) (isCompact_range hf).isBounded (isCompact_range hg).isBounded
  obtain ⟨z, ⟨b, rfl⟩, hb⟩ := exists_dist_lt_of_hausdorffDist_lt (mem_range_self a) hr hfin
  exact ⟨b, hb⟩
end PaperN.PartI
