import PaperN.PartII.DiameterContinuity
import PaperN.PartI.GHSection

namespace PaperN.PartII
open PaperN.PartI GromovHausdorff Metric Set Filter
open scoped Topology

/-- Intrinsic diameter on unmeasured GH classes. -/
noncomputable def ghDiameter (q : GHSpace) : ℝ :=
  diam (univ : Set (ghRepresentative q))

/-- The chosen representative computes the diameter of every whole carrier. -/
theorem ghDiameter_toGHSpace (X : MeasuredCompact.{0}) :
    ghDiameter (toGHSpace X) = diam (univ : Set X) := by
  obtain ⟨e⟩ := toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp (ghRepresentative_class (toGHSpace X))
  exact e.diam_univ

/-- Continuity uses only the existing ordinary GH common-embedding input. -/
theorem continuous_ghDiameter (hg : GHCommonEmbeddingInput.{0}) : Continuous ghDiameter := by
  apply continuous_iff_seqContinuous.mpr
  intro qs q hq
  have hx : Tendsto (fun k ↦ toGHSpace (ghRepresentative (qs k))) atTop
      (𝓝 (toGHSpace (ghRepresentative q))) := by
    simpa only [ghRepresentative_class] using hq
  obtain ⟨C, hH⟩ := hg (fun k ↦ ghRepresentative (qs k)) (ghRepresentative q) hx
  exact diameter_tendsto_of_commonRealization C hH

/-- The domain of the singleton zero model at tolerance tau. -/
def singletonModelDomain (τ : ℝ) : Set GHSpace := {q | ghDiameter q < τ}

theorem isOpen_singletonModelDomain (hg : GHCommonEmbeddingInput.{0}) (τ : ℝ) :
    IsOpen (singletonModelDomain τ) :=
  isOpen_lt (continuous_ghDiameter hg) continuous_const

theorem singleton_mem_singletonModelDomain (X : MeasuredCompact.{0}) [Subsingleton X]
    (τ : ℝ) (hτ : 0 < τ) : toGHSpace X ∈ singletonModelDomain τ := by
  change ghDiameter (toGHSpace X) < τ
  rw [ghDiameter_toGHSpace]
  simpa only [diam_subsingleton (Set.subsingleton_univ)] using hτ

/-- Every carrier in the open domain has strict zero-model approximation error. -/
theorem zeroCoordinatePair_error_on_singletonModelDomain
    (X : MeasuredCompact.{0}) (τ : ℝ) (hX : toGHSpace X ∈ singletonModelDomain τ) :
    (⨆ z : X × X, |(zeroCoordinatePair X).pseudometric z.1 z.2 - dist z.1 z.2|) < τ := by
  rw [zeroCoordinatePair_metric_error, ← ghDiameter_toGHSpace]
  exact hX

/-- The domain is an actual neighborhood of every singleton center. -/
theorem singletonModelDomain_mem_nhds (hg : GHCommonEmbeddingInput.{0})
    (X : MeasuredCompact.{0}) [Subsingleton X] (τ : ℝ) (hτ : 0 < τ) :
    singletonModelDomain τ ∈ 𝓝 (toGHSpace X) :=
  (isOpen_singletonModelDomain hg τ).mem_nhds
    (singleton_mem_singletonModelDomain X τ hτ)

/-- The error of every carrier representative is the continuous GH diameter. -/
theorem zeroCoordinatePair_metric_error_eq_ghDiameter (X : MeasuredCompact.{0}) :
    (⨆ z : X × X, |(zeroCoordinatePair X).pseudometric z.1 z.2 - dist z.1 z.2|) =
      ghDiameter (toGHSpace X) := by
  rw [zeroCoordinatePair_metric_error, ghDiameter_toGHSpace]

end PaperN.PartII
