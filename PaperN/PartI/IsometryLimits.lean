import PaperN.PartI.IsometryLimitsStatements
import PaperN.PartI.IsometryGraph
import Mathlib.Topology.TietzeExtension

namespace PaperN.PartI
open TopologicalSpace MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction
variable {Z : Type*} [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]

/-- Change variables for the already defined continuous probability pushforward. -/
theorem integral_probabilityPushforward {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (e : C(X, Z))
    (μ : ProbabilityMeasure X) (f : Z →ᵇ ℝ) :
    ∫ z, f z ∂(probabilityPushforward e μ : Measure Z) = ∫ x, f (e x) ∂(μ : Measure X) := by
  exact integral_map e.continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable

omit [BorelSpace Z] in
/-- A continuous test function vanishing on the limit graph vanishes uniformly on nearby graphs,
and therefore its integral tends to zero for every choice of probabilities on the carriers. -/
theorem graph_integral_error_tendsto
    (Ks : ℕ → NonemptyCompacts Z) (K : NonemptyCompacts Z)
    (gs : ∀ n, Ks n ≃ᵢ Ks n) (g : K ≃ᵢ K)
    (hG : Tendsto (fun n ↦ isometryGraph (Ks n) (gs n)) atTop (𝓝 (isometryGraph K g)))
    (f h : Z →ᵇ ℝ) (he : ∀ x : K, h (x : Z) = f (g x : Z))
    (μs : ∀ n, ProbabilityMeasure (Ks n)) :
    Tendsto (fun n ↦ ∫ x : Ks n, (f (gs n x : Z) - h (x : Z)) ∂(μs n : Measure (Ks n)))
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let U : Set (Z × Z) := {p | ‖f p.2 - h p.1‖ < ε / 2}
  have hU : IsOpen U := isOpen_lt (by fun_prop) continuous_const
  have hGU : (isometryGraph K g : Set (Z × Z)) ⊆ U := by
    intro p hp
    obtain ⟨x, rfl⟩ := (mem_isometryGraph K g p).mp hp
    change ‖f (g x : Z) - h (x : Z)‖ < ε / 2
    rw [he x, sub_self, norm_zero]
    exact half_pos hε
  have hev : ∀ᶠ n in atTop, (isometryGraph (Ks n) (gs n) : Set (Z × Z)) ⊆ U :=
    hG.eventually ((NonemptyCompacts.isOpen_subsets_of_isOpen hU).mem_nhds hGU)
  filter_upwards [hev] with n hn
  have hb : ∀ᵐ x : Ks n ∂(μs n : Measure (Ks n)), ‖f (gs n x : Z) - h (x : Z)‖ ≤ ε / 2 :=
    ae_of_all _ fun x ↦ (hn ((mem_isometryGraph (Ks n) (gs n) _).mpr ⟨x, rfl⟩)).le
  have hi := norm_integral_le_of_norm_le_const hb
  have hh : ‖∫ x : Ks n, (f (gs n x : Z) - h (x : Z)) ∂(μs n : Measure (Ks n))‖ ≤ ε / 2 := by
    simpa using hi
  simpa only [dist_zero_right] using lt_of_le_of_lt hh (half_lt_self hε)

/-- Graph convergence and weak convergence of the original probabilities imply weak convergence
of their isometric pushforwards. Tietze extends each real test function composed with the limit map. -/
theorem isometry_pushforward_tendsto
    (Ks : ℕ → NonemptyCompacts Z) (K : NonemptyCompacts Z)
    (gs : ∀ n, Ks n ≃ᵢ Ks n) (g : K ≃ᵢ K)
    (hG : Tendsto (fun n ↦ isometryGraph (Ks n) (gs n)) atTop (𝓝 (isometryGraph K g)))
    (μs : ∀ n, ProbabilityMeasure (Ks n)) (μ : ProbabilityMeasure K)
    (hμ : Tendsto (fun n ↦ probabilityPushforward (compactInclusion (Ks n)) (μs n))
      atTop (𝓝 (probabilityPushforward (compactInclusion K) μ))) :
    Tendsto (fun n ↦ probabilityPushforward (compactAction (Ks n) (gs n)) (μs n))
      atTop (𝓝 (probabilityPushforward (compactAction K g) μ)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  let fg := f.compContinuous (compactAction K g)
  obtain ⟨h, _, he⟩ := fg.exists_extension_norm_eq_of_isClosedEmbedding
    K.isCompact.isClosed.isClosedEmbedding_subtypeVal
  have he' : ∀ x : K, h (x : Z) = f (g x : Z) := fun x ↦ congrFun he x
  have hweak := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ h
  simp only [integral_probabilityPushforward] at hweak ⊢
  have herr := graph_integral_error_tendsto Ks K gs g hG f h he' μs
  have herr' : Tendsto (fun n ↦ (∫ x : Ks n, f (gs n x : Z) ∂(μs n : Measure (Ks n))) -
      ∫ x : Ks n, h (x : Z) ∂(μs n : Measure (Ks n))) atTop (𝓝 0) := by
    convert herr using 1
    funext n
    exact (integral_sub ((f.compContinuous (compactAction (Ks n) (gs n))).integrable (μs n : Measure (Ks n)))
      ((h.compContinuous (compactInclusion (Ks n))).integrable (μs n : Measure (Ks n)))).symm
  have hsum := herr'.add hweak
  simpa only [compactInclusion, compactAction, ContinuousMap.coe_mk, sub_add_cancel, zero_add, he'] using hsum

/-- Both conclusions of `lem:isometry-limits`, with the probabilities chosen after the subsequence. -/
theorem isometryLimits_spec [CompactSpace Z] : IsometryLimitsStatement (Z := Z) := by
  intro Ks K hK gs
  obtain ⟨φ, g, hφ, hG⟩ := isometryGraphSubsequence_spec Ks K hK gs
  exact ⟨φ, g, hφ, hG, fun μs μ hμ ↦
    isometry_pushforward_tendsto (fun n ↦ Ks (φ n)) K (fun n ↦ gs (φ n)) g hG μs μ hμ⟩

end PaperN.PartI
