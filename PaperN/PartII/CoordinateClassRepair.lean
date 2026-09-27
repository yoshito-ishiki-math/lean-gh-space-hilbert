import PaperN.PartII.NormedCoordinateClass
import Mathlib.Topology.Instances.Real.Lemmas

namespace PaperN.PartII
open Filter Topology PaperN.Shared
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] (Xs : ℕ → Type*) [∀ n, TopologicalSpace (Xs n)]

/-- Repair exceptional indices even when the initial candidate maps are not
continuous and the candidate seminorms are not definite. -/
theorem repair_coordinate_class_representatives
    (cs : ∀ n, NormedCoordinateClass (Xs n) E)
    (fs : ∀ n, Xs n → E) (ps : ℕ → Seminorm ℝ E)
    (hgood : ∀ᶠ n in atTop, ∃ a : NormedCoordinatePair (Xs n) E,
      Quotient.mk _ a = cs n ∧ (⇑a.coordinates = fs n) ∧ a.norm = ps n) :
    ∃ as : ∀ n, NormedCoordinatePair (Xs n) E,
      (∀ n, Quotient.mk _ (as n) = cs n) ∧
      ∀ᶠ n in atTop, (⇑(as n).coordinates = fs n) ∧ (as n).norm = ps n := by
  classical
  let good (n : ℕ) := ∃ a : NormedCoordinatePair (Xs n) E,
    Quotient.mk _ a = cs n ∧ (⇑a.coordinates = fs n) ∧ a.norm = ps n
  let as (n : ℕ) : NormedCoordinatePair (Xs n) E :=
    if h : good n then h.choose else (cs n).out
  refine ⟨as, ?_, ?_⟩
  · intro n
    by_cases h : good n
    · exact (by simpa [as, h] using h.choose_spec.1)
    · simp [as, h]
  · filter_upwards [hgood] with n hn
    have h : good n := hn
    simpa [as, h] using h.choose_spec.2

/-- Repair preserves both suprema used in model continuity for every fixed
correspondence sequence; the repaired pairs do not depend on that sequence. -/
theorem coordinate_class_repair_preserves_suprema
    (as : ∀ n, NormedCoordinatePair (Xs n) E)
    (fs : ∀ n, Xs n → E) (ps : ℕ → Seminorm ℝ E)
    (heq : ∀ᶠ n in atTop, (⇑(as n).coordinates = fs n) ∧ (as n).norm = ps n)
    (a : NormedCoordinatePair X E)
    (hn : Tendsto (fun n ↦ unitNormError (ps n) a.norm) atTop (𝓝 0)) :
    Tendsto (fun n ↦ unitNormError (as n).norm a.norm) atTop (𝓝 0) ∧
    ∀ (R : ∀ n, Correspondence (Xs n) X),
      Tendsto (fun n ↦ ⨆ z : (R n).rel, ‖fs n z.val.1 - a.coordinates z.val.2‖)
        atTop (𝓝 0) →
      Tendsto (fun n ↦ coordinateError (R n) (as n).coordinates a.coordinates)
        atTop (𝓝 0) := by
  constructor
  · apply hn.congr'
    filter_upwards [heq] with n h
    rw [h.2]
  · intro R hR
    apply hR.congr'
    filter_upwards [heq] with n h
    simp only [coordinateError, h.1]

end PaperN.PartII
