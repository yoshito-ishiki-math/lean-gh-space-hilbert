import PaperN.PartII.CompactEigenvalueInput
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Order.Interval.Set.Infinite

namespace PaperN.PartII
open MeasureTheory Metric Set
universe u
section Complexification
variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Multiplication by i on the real model H × H of H ⊕ iH. -/
def complexStructure : (H × H) →L[ℝ] (H × H) :=
  (-ContinuousLinearMap.snd ℝ H H).prod (ContinuousLinearMap.fst ℝ H H)

/-- zI - T_C in real block coordinates. The product norm gives the same
bounded maps as the Hilbert complexification norm. -/
def complexResolventBlock (T : H →L[ℝ] H) (z : ℂ) : (H × H) →L[ℝ] (H × H) :=
  (z.re • (1 : H →L[ℝ] H) - T).prodMap
    (z.re • (1 : H →L[ℝ] H) - T) + z.im • complexStructure

/-- Spectrum of the complexification, expressed through bounded complex-linear
inverses in real coordinates. A real-linear map is complex-linear precisely when
it commutes with multiplication by i. No real-algebra spectrum is substituted. -/
def complexifiedSpectrum (T : H →L[ℝ] H) : Set ℂ :=
  {z | ¬ ∃ S : (H × H) →L[ℝ] (H × H),
    S * complexResolventBlock T z = 1 ∧ complexResolventBlock T z * S = 1 ∧
    S * complexStructure = complexStructure * S}

/-- Real resolvent points lift to the complexification by applying their bounded
inverse separately to real and imaginary components. -/
theorem ofReal_not_mem_complexifiedSpectrum (T : H →L[ℝ] H) {a : ℝ}
    (ha : a ∉ spectrum ℝ T) : (a : ℂ) ∉ complexifiedSpectrum T := by
  have hu : IsUnit (a • (1 : H →L[ℝ] H) - T) := by
    simpa [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one] using ha
  obtain ⟨U,hU⟩ := hu
  have hl (x : H) : (↑(U⁻¹) : H →L[ℝ] H) ((U : H →L[ℝ] H) x) = x := by
    change ((↑(U⁻¹) : H →L[ℝ] H) * ↑U) x = x
    simp
  have hr (x : H) : (U : H →L[ℝ] H) ((↑(U⁻¹) : H →L[ℝ] H) x) = x := by
    change ((U : H →L[ℝ] H) * ↑(U⁻¹)) x = x
    simp
  change ¬ ¬ ∃ S : (H × H) →L[ℝ] (H × H), _
  apply not_not.mpr
  refine ⟨(↑(U⁻¹) : H →L[ℝ] H).prodMap ↑(U⁻¹), ?_, ?_, ?_⟩
  · ext p <;> simp [complexResolventBlock, ← hU, hl]
  · ext p <;> simp [complexResolventBlock, ← hU, hr]
  · ext p <;> simp [complexStructure, mul_apply_eq_comp]
/-- The real-coordinate action of a complex scalar. -/
def complexScalar (z : ℂ) : (H × H) →L[ℝ] (H × H) :=
  z.re • (1 : (H × H) →L[ℝ] (H × H)) + z.im • complexStructure

theorem complexScalar_apply (z : ℂ) (p : H × H) :
    complexScalar z p = (z.re • p.1 - z.im • p.2, z.im • p.1 + z.re • p.2) := by
  apply Prod.ext <;> simp [complexScalar, complexStructure, sub_eq_add_neg, add_comm]

/-- Commutation with i is exactly complex linearity of a real-linear map. -/
theorem commutes_complexStructure_iff (S : (H × H) →L[ℝ] (H × H)) :
    S * complexStructure = complexStructure * S ↔
      ∀ (z : ℂ) (p : H × H), S (complexScalar z p) = complexScalar z (S p) := by
  constructor
  · intro h z p
    have hp := congrArg (fun F : (H × H) →L[ℝ] (H × H) ↦ F p) h
    simp only [mul_apply_eq_comp] at hp
    simp [complexScalar, hp]
  · intro h
    apply ContinuousLinearMap.ext
    intro p
    simpa [complexScalar] using h Complex.I p

/-- A directly reviewable inverse criterion using the actual complex scalar action. -/
theorem not_mem_complexifiedSpectrum_iff (T : H →L[ℝ] H) (z : ℂ) :
    z ∉ complexifiedSpectrum T ↔ ∃ S : (H × H) →L[ℝ] (H × H),
      S * complexResolventBlock T z = 1 ∧ complexResolventBlock T z * S = 1 ∧
      ∀ (w : ℂ) (p : H × H), S (complexScalar w p) = complexScalar w (S p) := by
  simp only [complexifiedSpectrum, Set.mem_setOf_eq, not_not,
    commutes_complexStructure_iff]

theorem complexResolventBlock_apply (T : H →L[ℝ] H) (z : ℂ) (p : H × H) :
    complexResolventBlock T z p = complexScalar z p - (T p.1, T p.2) := by
  ext <;> simp [complexResolventBlock, complexScalar, complexStructure] <;> abel
end Complexification
section Avoidance
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Every interval (0,δ) contains a cutoff avoiding both complexified spectral endpoints. -/
theorem exists_complexified_spectral_gap (hs : CompactEigenvalueFinitenessInput.{u})
    (T : H →L[ℝ] H) (hc : IsCompactOperator T) (ha : IsSelfAdjoint T)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η < δ ∧ (η : ℂ) ∉ complexifiedSpectrum T ∧
      ((-η : ℝ) : ℂ) ∉ complexifiedSpectrum T := by
  have hf := (hs H T hc ha (δ/2) (by positivity)).image (fun a : ℝ ↦ |a|)
  obtain ⟨η,hη,havoid⟩ := (Set.Ioo_infinite (show δ/2 < δ by linarith)).exists_notMem_finite hf
  have hpos : 0 < η := lt_trans (by positivity : 0 < δ/2) hη.1
  have hne : ¬ Module.End.HasEigenvalue T.toLinearMap η := by
    intro he
    apply havoid
    exact ⟨η,⟨by simpa [abs_of_pos hpos] using hη.1,he⟩,abs_of_pos hpos⟩
  have hnne : ¬ Module.End.HasEigenvalue T.toLinearMap (-η) := by
    intro he
    apply havoid
    exact ⟨-η,⟨by simpa [abs_neg,abs_of_pos hpos] using hη.1,he⟩,
      by simp [abs_neg,abs_of_pos hpos]⟩
  refine ⟨η,hpos,hη.2,ofReal_not_mem_complexifiedSpectrum T ?_,
    ofReal_not_mem_complexifiedSpectrum T ?_⟩
  · exact (hc.hasEigenvalue_iff_mem_spectrum (ne_of_gt hpos)).not.mp hne
  · exact (hc.hasEigenvalue_iff_mem_spectrum (neg_ne_zero.mpr (ne_of_gt hpos))).not.mp hnne
end Avoidance
end PaperN.PartII
