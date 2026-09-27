import PaperN.Shared.PseudometricComparison

namespace PaperN.Shared
open Set Metric GromovHausdorff
universe u v

theorem distortionLE_iff {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
    [Nonempty X] [Nonempty Y] (R : Correspondence X Y) (a : ℝ) :
    R.DistortionLE a ↔ R.distortion ≤ a := by
  constructor
  · intro h
    exact ciSup_le (fun z ↦ h z.1 z.2)
  · intro h p q
    exact (le_error R (ContinuousPseudometric.ofMetric X)
      (ContinuousPseudometric.ofMetric Y) p q).trans h

theorem correspondenceEmbedding_sup_spec : CorrespondenceEmbeddingSupStatement.{u,v} := by
  intro X Y _ _ _ _ _ _ R ε hε hR
  exact correspondenceEmbedding_spec X Y R ε hε ((distortionLE_iff R (2*ε)).mpr hR)
end PaperN.Shared
