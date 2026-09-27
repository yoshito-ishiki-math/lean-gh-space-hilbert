import PaperN.PartI.ParameterIntegrals
import PaperN.PartI.GHPExternal
import PaperN.PartI.CommonIsometryGraph

namespace PaperN.PartI
open MeasureTheory Set Filter TopologicalSpace Metric
open scoped Topology
variable {Z : Type*} [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z]

noncomputable def ballMass (μ : ProbabilityMeasure Z) (r : ℝ) (x : Z) : ℝ :=
  ∫ y, metricBump x r y ∂(μ : Measure Z)

omit [BorelSpace Z] [CompactSpace Z] in
lemma ballMass_nonneg (μ : ProbabilityMeasure Z) (r : ℝ) (x : Z) : 0 ≤ ballMass μ r x :=
  integral_nonneg fun y ↦ metricBump_nonneg x y r

lemma continuous_ballMass (μ : ProbabilityMeasure Z) (r : ℝ) : Continuous (ballMass μ r) := by
  have h : Continuous (fun p : Z × Z ↦ metricBump p.1 r p.2) := by
    unfold metricBump; fun_prop
  change Continuous (fun x ↦ ∫ y, metricBump x r y ∂(μ : Measure Z))
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous (μ := (μ : Measure Z)) h isCompact_univ)

noncomputable def minimumBallMass (μ : ProbabilityMeasure Z) (r : ℝ) : ℝ :=
  ⨅ x, ballMass μ r x

omit [BorelSpace Z] [CompactSpace Z] in
lemma minimumBallMass_le (μ : ProbabilityMeasure Z) (r : ℝ) (x : Z) :
    minimumBallMass μ r ≤ ballMass μ r x := by
  apply ciInf_le
  exact ⟨0, by rintro _ ⟨y, rfl⟩; exact ballMass_nonneg μ r y⟩

lemma minimumBallMass_attained [Nonempty Z] (μ : ProbabilityMeasure Z) (r : ℝ) :
    ∃ x, ballMass μ r x = minimumBallMass μ r := by
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty)
    (continuous_ballMass μ r).continuousOn
  exact ⟨x, le_antisymm (le_ciInf fun y ↦ hx (mem_univ y)) (minimumBallMass_le μ r x)⟩

lemma minimumBallMass_pos_iff [Nonempty Z] (μ : ProbabilityMeasure Z) (r : ℝ) :
    0 < minimumBallMass μ r ↔ ∀ x, 0 < ballMass μ r x := by
  constructor
  · exact fun h x ↦ h.trans_le (minimumBallMass_le μ r x)
  · intro h
    obtain ⟨x, hx⟩ := minimumBallMass_attained μ r
    rw [← hx]
    exact h x

omit [CompactSpace Z] in
/-- Isometric embedding commutes with the ambient bump integral. -/
lemma ballMass_map {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] (μ : ProbabilityMeasure X) (e : X → Z) (he : Isometry e)
    (r : ℝ) (x : X) :
    ballMass (μ.map he.continuous.measurable.aemeasurable) r (e x) = ballMass μ r x := by
  unfold ballMass
  change (∫ y, metricBump (e x) r y ∂(Measure.map e (μ : Measure X))) = _
  rw [integral_map he.continuous.measurable.aemeasurable
    (continuous_metricBump (e x) r).aestronglyMeasurable]
  congr 1
  funext y
  simp only [metricBump, he.dist_eq]

omit [CompactSpace Z] in
/-- The minimum uses the entire carrier and is preserved by measured isometries. -/
lemma minimumBallMass_isometryEquiv {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] [Nonempty Z]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Z) (e : X ≃ᵢ Z)
    (he : Measure.map e (μ : Measure X) = (ν : Measure Z)) (r : ℝ) :
    minimumBallMass μ r = minimumBallMass ν r := by
  have hp : μ.map e.continuous.measurable.aemeasurable = ν :=
    ProbabilityMeasure.toMeasure_injective he
  have hb : ∀ x, ballMass ν r (e x) = ballMass μ r x := by
    intro x
    rw [← hp]
    exact ballMass_map μ e e.isometry r x
  apply le_antisymm
  · apply le_ciInf
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [hb]
    exact minimumBallMass_le μ r x
  · apply le_ciInf
    intro x
    rw [← hb]
    exact minimumBallMass_le ν r (e x)

omit [CompactSpace Z] in
/-- A minimum over the whole carrier is the minimum of the ambient integral over its image. -/
lemma minimumBallMass_range {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X]
    (μ : ProbabilityMeasure X) (e : X → Z) (he : Isometry e) (r : ℝ) :
    (∃ z ∈ range e, ballMass (μ.map he.continuous.measurable.aemeasurable) r z = minimumBallMass μ r) ∧
    ∀ z ∈ range e, minimumBallMass μ r ≤ ballMass (μ.map he.continuous.measurable.aemeasurable) r z := by
  constructor
  · obtain ⟨x, hx⟩ := minimumBallMass_attained μ r
    exact ⟨e x, ⟨x, rfl⟩, (ballMass_map μ e he r x).trans hx⟩
  · rintro _ ⟨x, rfl⟩
    rw [ballMass_map μ e he r x]
    exact minimumBallMass_le μ r x

/-- Full support is detected by positive minima at the cofinal dyadic radii. -/
lemma support_eq_univ_iff_minimumBallMass_pos [Nonempty Z] (μ : ProbabilityMeasure Z) :
    (μ : Measure Z).support = univ ↔ ∀ n : ℕ, 0 < minimumBallMass μ ((1 / 2 : ℝ) ^ n) := by
  constructor
  · intro h n
    haveI := openPos_of_support_eq_univ (μ : Measure Z) h
    apply (minimumBallMass_pos_iff μ _).mpr
    intro x
    exact metricBump_integral_pos (μ : Measure Z) x (by positivity)
  · intro h
    apply Set.eq_univ_of_forall
    intro x
    rw [Measure.mem_support_iff_forall]
    intro U hU
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (show (1 / 2 : ℝ) < 1 by norm_num)
    have hpos := (minimumBallMass_pos_iff μ _).mp (h n) x
    have hb := (metricBump_integral_bounds (μ : Measure Z) x
      (show 0 < (1 / 2 : ℝ) ^ n by positivity)).2
    have hm : 0 < (μ : Measure Z) (ball x ((1 / 2 : ℝ) ^ n)) :=
      (ENNReal.toReal_pos_iff.mp (lt_of_lt_of_le hpos hb)).1
    exact hm.trans_le (measure_mono ((ball_subset_ball hn.le).trans hball))

end PaperN.PartI
