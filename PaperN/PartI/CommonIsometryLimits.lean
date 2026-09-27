import PaperN.PartI.CommonIsometryGraph
import PaperN.PartI.IsometryLimits

namespace PaperN.PartI
open MeasureTheory TopologicalSpace Set Filter
open scoped Topology BoundedContinuousFunction
universe u
namespace CommonRealization
variable {Xs : ℕ → MeasuredCompact.{u}} {X : MeasuredCompact.{u}}

noncomputable def seqActionProbability (C : CommonRealization Xs X)
    (gs : ∀ n, Xs n ≃ᵢ Xs n) (n : ℕ) : ProbabilityMeasure C :=
  (Xs n).probability.map (C.seqMap n ∘ gs n)
noncomputable def limitActionProbability (C : CommonRealization Xs X)
    (g : X ≃ᵢ X) : ProbabilityMeasure C :=
  X.probability.map (C.limitMap ∘ g)

def subsequence (C : CommonRealization Xs X) (φ : ℕ → ℕ) :
    CommonRealization (fun n ↦ Xs (φ n)) X where
  Carrier := C
  metric := inferInstance
  compact := inferInstance
  seqMap n := C.seqMap (φ n)
  limitMap := C.limitMap
  seq_isometry n := C.seq_isometry (φ n)
  limit_isometry := C.limit_isometry

/-- Directly on the original carriers: graph convergence controls all test-integral errors. -/
theorem graph_integral_error (C : CommonRealization Xs X)
    (gs : ∀ n, Xs n ≃ᵢ Xs n) (g : X ≃ᵢ X)
    (hG : Tendsto (fun n ↦ C.seqGraph n (gs n)) atTop (𝓝 (C.limitGraph g)))
    (f h : C →ᵇ ℝ) (he : ∀ x : X, h (C.limitMap x) = f (C.limitMap (g x))) :
    Tendsto (fun n ↦ ∫ x : Xs n, (f (C.seqMap n (gs n x)) - h (C.seqMap n x))
      ∂((Xs n).probability : Measure (Xs n))) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let U : Set (C × C) := {p | ‖f p.2 - h p.1‖ < ε / 2}
  have hU : IsOpen U := isOpen_lt (by fun_prop) continuous_const
  have hGU : (C.limitGraph g : Set (C × C)) ⊆ U := by
    intro p hp
    obtain ⟨x, rfl⟩ := (C.mem_limitGraph g p).mp hp
    change ‖f (C.limitMap (g x)) - h (C.limitMap x)‖ < ε / 2
    rw [he x, sub_self, norm_zero]
    exact half_pos hε
  have hev := hG.eventually ((NonemptyCompacts.isOpen_subsets_of_isOpen hU).mem_nhds hGU)
  filter_upwards [hev] with n hn
  have hb : ∀ᵐ x : Xs n ∂((Xs n).probability : Measure (Xs n)),
      ‖f (C.seqMap n (gs n x)) - h (C.seqMap n x)‖ ≤ ε / 2 :=
    ae_of_all _ fun x ↦ (hn ((C.mem_seqGraph n (gs n) _).mpr ⟨x, rfl⟩)).le
  have hi : ‖∫ x : Xs n, (f (C.seqMap n (gs n x)) - h (C.seqMap n x))
      ∂((Xs n).probability : Measure (Xs n))‖ ≤ ε / 2 := by
    simpa using norm_integral_le_of_norm_le_const hb
  simpa only [dist_zero_right] using hi.trans_lt (half_lt_self hε)

/-- The pushforward part of the isometry-limit lemma on original measured carriers. -/
theorem actionProbability_tendsto (C : CommonRealization Xs X)
    (gs : ∀ n, Xs n ≃ᵢ Xs n) (g : X ≃ᵢ X)
    (hG : Tendsto (fun n ↦ C.seqGraph n (gs n)) atTop (𝓝 (C.limitGraph g)))
    (hW : C.WeakConverges) :
    Tendsto (C.seqActionProbability gs) atTop (𝓝 (C.limitActionProbability g)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  let fg := f.compContinuous ⟨fun x ↦ C.limitMap (g x), C.limit_isometry.continuous.comp g.continuous⟩
  obtain ⟨h, _, he⟩ := fg.exists_extension_norm_eq_of_isClosedEmbedding C.limit_isometry.isClosedEmbedding
  have he' : ∀ x, h (C.limitMap x) = f (C.limitMap (g x)) := fun x ↦ congrFun he x
  have hw := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hW h
  have herr := C.graph_integral_error gs g hG f h he'
  simp only [seqProbability, limitProbability, ProbabilityMeasure.toMeasure_map] at hw
  simp_rw [integral_map (C.seq_isometry _).continuous.measurable.aemeasurable
    h.continuous.aestronglyMeasurable,
    integral_map C.limit_isometry.continuous.measurable.aemeasurable
      h.continuous.aestronglyMeasurable] at hw
  simp only [seqActionProbability, limitActionProbability, ProbabilityMeasure.toMeasure_map]
  simp_rw [integral_map ((C.seq_isometry _).continuous.comp (gs _).continuous).measurable.aemeasurable
    f.continuous.aestronglyMeasurable,
    integral_map (C.limit_isometry.continuous.comp g.continuous).measurable.aemeasurable
      f.continuous.aestronglyMeasurable]
  have herr' : Tendsto (fun n ↦
      (∫ x : Xs n, f (C.seqMap n (gs n x)) ∂((Xs n).probability : Measure (Xs n))) -
      ∫ x : Xs n, h (C.seqMap n x) ∂((Xs n).probability : Measure (Xs n))) atTop (𝓝 0) := by
    convert herr using 1
    funext n
    exact (integral_sub
      ((f.compContinuous ⟨_, (C.seq_isometry n).continuous.comp (gs n).continuous⟩).integrable _)
      ((h.compContinuous ⟨_, (C.seq_isometry n).continuous⟩).integrable _)).symm
  simpa only [sub_add_cancel, zero_add, he', Function.comp_def] using herr'.add hw

/-- Select the same isometry subsequence for the graph and its pushed probability. -/
theorem actionProbability_subsequence (C : CommonRealization Xs X)
    (hH : C.HausdorffConverges) (hW : C.WeakConverges) (gs : ∀ n, Xs n ≃ᵢ Xs n) :
    ∃ (φ : ℕ → ℕ) (g : X ≃ᵢ X), StrictMono φ ∧
      Tendsto (fun n ↦ C.seqActionProbability gs (φ n)) atTop (𝓝 (C.limitActionProbability g)) := by
  obtain ⟨φ, g, hφ, hG⟩ := C.isometryGraph_subsequence hH gs
  exact ⟨φ, g, hφ, (C.subsequence φ).actionProbability_tendsto
    (fun n ↦ gs (φ n)) g hG (hW.comp hφ.tendsto_atTop)⟩
end CommonRealization
end PaperN.PartI
