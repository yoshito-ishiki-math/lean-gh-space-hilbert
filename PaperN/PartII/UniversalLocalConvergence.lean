import PaperN.PartII.UniversalLocalClass
import PaperN.PartII.CorrespondenceTransport

namespace PaperN.PartII.LocalModel
open PaperN.Shared PaperN.PartI GromovHausdorff Set Metric Filter
open scoped Topology

/-- A4 on arbitrary carrier universes, with representatives chosen before correspondences. -/
theorem universal_representatives_converge
    {X₀ : MeasuredCompact.{0}} {τ : ℝ} (M : LocalModel X₀ τ)
    (Xs : ℕ → Type*) (X Z : Type*)
    [∀ n, MetricSpace (Xs n)] [∀ n, CompactSpace (Xs n)] [∀ n, Nonempty (Xs n)]
    [MetricSpace X] [CompactSpace X] [Nonempty X] [MetricSpace Z] [CompactSpace Z]
    (es : ∀ n, Xs n → Z) (e : X → Z) (hes : ∀ n, Isometry (es n)) (he : Isometry e)
    (hXs : ∀ n, toGHSpace (Xs n) ∈ M.domain) (hX : toGHSpace X ∈ M.domain)
    (hH : Tendsto (fun n ↦ hausdorffDist (range (es n)) (range e)) atTop (𝓝 0)) :
    ∃ a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin M.dimension)),
      ∃ as : ∀ n, NormedCoordinatePair (Xs n) (EuclideanSpace ℝ (Fin M.dimension)),
        Quotient.mk _ a = M.universalClass X hX ∧
        (∀ n, Quotient.mk _ (as n) = M.universalClass (Xs n) (hXs n)) ∧
        Tendsto (fun n ↦ unitNormError (as n).norm a.norm) atTop (𝓝 0) ∧
        ∀ R : ∀ n, Correspondence (Xs n) X,
          Tendsto (fun n ↦ ⨆ z : (R n).rel, dist (es n z.val.1) (e z.val.2)) atTop (𝓝 0) →
          Tendsto (fun n ↦ coordinateError (R n) (as n).coordinates a.coordinates) atTop (𝓝 0) := by
  letI : Nonempty Z := ⟨e (Classical.choice inferInstance)⟩
  let C : CommonRealization (fun n ↦ smallCarrier (Xs n)) (smallCarrier X) := {
    Carrier := smallCarrier Z
    metric := inferInstance
    compact := inferInstance
    seqMap := fun n ↦ (smallCarrierEquiv Z).symm ∘ es n ∘ smallCarrierEquiv (Xs n)
    limitMap := (smallCarrierEquiv Z).symm ∘ e ∘ smallCarrierEquiv X
    seq_isometry := fun n ↦ (smallCarrierEquiv Z).symm.isometry.comp
      ((hes n).comp (smallCarrierEquiv (Xs n)).isometry)
    limit_isometry := (smallCarrierEquiv Z).symm.isometry.comp
      (he.comp (smallCarrierEquiv X).isometry) }
  have hC : C.HausdorffConverges := by
    simpa only [CommonRealization.HausdorffConverges, C, PaperN.PartI.small_range,
      hausdorffDist_image (smallCarrierEquiv Z).symm.isometry] using hH
  have hs : ∀ n, toGHSpace (smallCarrier (Xs n)) ∈ M.domain := by
    simpa only [smallCarrier, ghRepresentative_class] using hXs
  have hx : toGHSpace (smallCarrier X) ∈ M.domain := by
    simpa only [smallCarrier, ghRepresentative_class] using hX
  obtain ⟨b, bs, hb, hbs, hn, hc⟩ := M.representatives_converge _ _ hs hx C hC
  let a := b.comap ⟨(smallCarrierEquiv X).symm, (smallCarrierEquiv X).symm.continuous⟩
  let as := fun n ↦ (bs n).comap
    ⟨(smallCarrierEquiv (Xs n)).symm, (smallCarrierEquiv (Xs n)).symm.continuous⟩
  refine ⟨a, as, ?_, ?_, hn, ?_⟩
  · exact congrArg (fun q ↦ NormedCoordinateClass.comap
      ⟨(smallCarrierEquiv X).symm, (smallCarrierEquiv X).symm.continuous⟩ q) hb
  · intro n
    exact congrArg (fun q ↦ NormedCoordinateClass.comap
      ⟨(smallCarrierEquiv (Xs n)).symm, (smallCarrierEquiv (Xs n)).symm.continuous⟩ q) (hbs n)
  intro R hR
  let S := fun n ↦ (R n).comapEquiv (smallCarrierEquiv (Xs n)).toEquiv
    (smallCarrierEquiv X).toEquiv
  have hS : Tendsto (fun n ↦ ⨆ z : (S n).rel,
      dist (C.seqMap n z.val.1) (C.limitMap z.val.2)) atTop (𝓝 0) := by
    convert hR using 1
    funext n
    change (⨆ z : (S n).rel, dist ((smallCarrierEquiv Z).symm (es n (smallCarrierEquiv (Xs n) z.val.1)))
      ((smallCarrierEquiv Z).symm (e (smallCarrierEquiv X z.val.2)))) = _
    simp only [(smallCarrierEquiv Z).symm.dist_eq]
    exact (R n).iSup_comapEquiv _ _ (fun x y ↦ dist (es n x) (e y))
  have h := hc S hS
  convert h using 1
  funext n
  symm
  unfold coordinateError
  apply (R n).comapEquivRel (smallCarrierEquiv (Xs n)).toEquiv
    (smallCarrierEquiv X).toEquiv |>.iSup_congr
  intro z
  simp [a, as, NormedCoordinatePair.comap, Correspondence.comapEquivRel]

end PaperN.PartII.LocalModel
