import PaperN.PartIV.BanachHomeomorphism
import Mathlib.Topology.Algebra.Module.Basic

namespace PaperN.PartIV
open Set TopologicalSpace Filter
open scoped ENNReal

/-- Real sequence spaces with the usual ℓᵖ norm. -/
abbrev RealSequenceSpace (p : ℝ≥0∞) := lp (fun _ : ℕ ↦ ℝ) p

/-- The coordinate unit vectors are linearly independent at every exponent. -/
theorem realSequence_units_independent (p : ℝ≥0∞) :
    LinearIndependent ℝ (fun i : ℕ ↦ (lp.single p i (1 : ℝ) : RealSequenceSpace p)) := by
  apply linearIndependent_iff'.mpr
  intro s g h i hi
  have he := congrArg (lp.evalₗ (𝕜 := ℝ) (fun _ : ℕ ↦ ℝ) p i) h
  simpa [map_sum, map_smul, lp.evalₗ_apply, lp.single_apply, Pi.single_apply, hi] using he


/-- Infinitely many coordinate unit vectors rule out finite dimension. -/
theorem realSequence_not_finiteDimensional (p : ℝ≥0∞) :
    ¬ FiniteDimensional ℝ (RealSequenceSpace p) := by
  intro h
  letI := h
  exact Module.Finite.not_linearIndependent_of_infinite
    (fun i : ℕ ↦ (lp.single p i (1 : ℝ) : RealSequenceSpace p))
    (realSequence_units_independent p)

/-- Finite-p sequence spaces are separable: the countable coordinate span is dense. -/
theorem realSequence_separable (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    SeparableSpace (RealSequenceSpace p) := by
  let v (i : ℕ) : RealSequenceSpace p := lp.single p i 1
  let S := Submodule.span ℝ (range v)
  have hs : IsSeparable (closure (S : Set (RealSequenceSpace p))) :=
    (countable_range v).isSeparable.span.closure
  apply isSeparable_univ_iff.mp
  apply hs.mono
  intro f _
  apply isClosed_closure.mem_of_tendsto (lp.hasSum_single hp f)
  apply Filter.Eventually.of_forall
  intro s
  apply subset_closure
  apply S.sum_mem
  intro i _
  have hv : v i ∈ S := Submodule.subset_span (mem_range_self i)
  have hm := S.smul_mem (f i) hv
  simpa [v, ← lp.single_smul] using hm

/-- Each ℓᵖ for 1 ≤ p < ∞ is a concrete target of the Banach-space consequence. -/
theorem ghSpace_homeomorphic_realSequence
    (h : Nonempty (GromovHausdorff.GHSpace ≃ₜ RealHilbertSpace))
    (hK : KadetsHomeomorphismInput) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hfin : p ≠ ⊤) :
    Nonempty (GromovHausdorff.GHSpace ≃ₜ RealSequenceSpace p) := by
  letI : SeparableSpace (RealSequenceSpace p) := realSequence_separable p hfin
  exact ghSpace_homeomorphic_banach_of_homeomorph h hK (RealSequenceSpace p)
    (realSequence_not_finiteDimensional p)

/-- The Hilbert model used in the Kadets specialization is separable. -/
theorem realHilbert_separable : SeparableSpace RealHilbertSpace :=
  realSequence_separable 2 (by norm_num)

/-- The Hilbert model used in the Kadets specialization is infinite dimensional. -/
theorem realHilbert_not_finiteDimensional : ¬ FiniteDimensional ℝ RealHilbertSpace :=
  realSequence_not_finiteDimensional 2

end PaperN.PartIV
