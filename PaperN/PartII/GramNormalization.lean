import PaperN.PartII.GramPositive
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

namespace PaperN.PartII
open Matrix Filter
open scoped Topology MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def gramNormalizer (G : Matrix ι ι ℝ) : Matrix ι ι ℝ := (CFC.sqrt G)⁻¹

theorem gramNormalizer_identity (G : Matrix ι ι ℝ) (hG : G.PosDef) :
    (gramNormalizer G).transpose * G * gramNormalizer G = 1 := by
  have hs : (CFC.sqrt G).PosSemidef := (CFC.sqrt_nonneg G).posSemidef
  have hu : IsUnit (CFC.sqrt G) := (CFC.isUnit_sqrt_iff G hG.posSemidef.nonneg).mpr hG.isUnit
  have ht : (gramNormalizer G).transpose = gramNormalizer G := by
    simpa only [gramNormalizer, Matrix.conjTranspose_eq_transpose_of_trivial] using hs.1.inv.eq
  rw [ht]
  unfold gramNormalizer
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hu
  calc
    _ = (CFC.sqrt G)⁻¹ * (CFC.sqrt G * CFC.sqrt G) * (CFC.sqrt G)⁻¹ := by
      congr 2
      exact (CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg).symm
    _ = 1 := by rw [← mul_assoc, Matrix.nonsing_inv_mul _ hd, one_mul, Matrix.mul_nonsing_inv _ hd]

theorem gramNormalizer_tendsto_one (Gs : ℕ → Matrix ι ι ℝ)
    (hG : Tendsto Gs atTop (𝓝 1)) (hpos : ∀ n, (Gs n).PosSemidef) :
    Tendsto (fun n ↦ gramNormalizer (Gs n)) atTop (𝓝 1) := by
  have hs : Tendsto (fun n ↦ CFC.sqrt (Gs n)) atTop (𝓝 (1 : Matrix ι ι ℝ)) := by
    have hc := CFC.continuousOn_sqrt (A := Matrix ι ι ℝ) 1 (show (1 : Matrix ι ι ℝ) ∈ {a | 0 ≤ a} from by
      change (0 : Matrix ι ι ℝ) ≤ 1
      exact zero_le_one)
    have ht := hc.tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hG, Filter.Eventually.of_forall fun n ↦ (hpos n).nonneg⟩)
    simpa only [Function.comp_def, CFC.sqrt_one] using ht
  have hi : ContinuousAt (Inv.inv : Matrix ι ι ℝ → Matrix ι ι ℝ) 1 := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (by simp)
  simpa only [Function.comp_def, gramNormalizer, inv_one] using hi.tendsto.comp hs

open MeasureTheory
variable {Z : Type*} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]

noncomputable def normalizeContinuousFamily (μ : ProbabilityMeasure Z) (v : ι → C(Z, ℝ)) :=
  transformContinuousBasis (gramNormalizer (continuousGram μ v)) v

theorem normalizeContinuousFamily_gram (μ : ProbabilityMeasure Z) (v : ι → C(Z, ℝ))
    (hG : (continuousGram μ v).PosDef) :
    continuousGram μ (normalizeContinuousFamily μ v) = 1 := by
  rw [normalizeContinuousFamily, continuousGram_transform]
  exact gramNormalizer_identity _ hG

theorem normalizeContinuousFamily_tendsto
    (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z)
    (hμ : Tendsto μs atTop (𝓝 μ)) (vs : ℕ → ι → C(Z, ℝ)) (v : ι → C(Z, ℝ))
    (hv : ∀ i, Tendsto (fun n ↦ vs n i) atTop (𝓝 (v i)))
    (horth : continuousGram μ v = 1) (i : ι) :
    Tendsto (fun n ↦ normalizeContinuousFamily (μs n) (vs n) i) atTop (𝓝 (v i)) := by
  apply transformContinuousBasis_tendsto_identity
  · apply gramNormalizer_tendsto_one
    · simpa only [horth] using continuousGram_tendsto μs μ hμ vs v hv
    · exact fun n ↦ continuousGram_posSemidef (μs n) (vs n)
  · exact hv

theorem normalizeContinuousFamily_eventually_gram
    (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z)
    (hμ : Tendsto μs atTop (𝓝 μ)) (vs : ℕ → ι → C(Z, ℝ)) (v : ι → C(Z, ℝ))
    (hv : ∀ i, Tendsto (fun n ↦ vs n i) atTop (𝓝 (v i)))
    (horth : continuousGram μ v = 1) :
    ∀ᶠ n in atTop, continuousGram (μs n) (normalizeContinuousFamily (μs n) (vs n)) = 1 := by
  filter_upwards [continuousGram_eventually_posDef μs μ hμ vs v hv horth] with n hn
  exact normalizeContinuousFamily_gram (μs n) (vs n) hn

end PaperN.PartII
