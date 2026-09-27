import PaperN.PartII.ModelSupConvergence

namespace PaperN.PartII.AmbientKernel
open MeasureTheory Filter PaperN.PartI ComplexKernel
open scoped Topology

theorem selected_spectral_model_sup_convergence
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm)
    {Xs : ℕ → MeasuredCompact.{0}} {X : MeasuredCompact.{0}} (C : CommonRealization Xs X)

    (hf : CompactEigenvalueFinitenessInput.{0})
     (hH : C.HausdorffConverges) (η : ℝ) (hη : 0 < η)
    (hpos : (η : ℂ) ∈ resolventSet ℂ
      (ComplexKernel.distanceOperator (selectedProbability hm hs X : Measure X)))
    (hneg : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ
      (ComplexKernel.distanceOperator (selectedProbability hm hs X : Measure X)))
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (v : ι → C(X, ℝ))
    (hv : ∀ i, v i ∈ spectralCutoff (selectedProbability hm hs X : Measure X) η)
    (ho : Orthonormal ℝ (fun i ↦ PaperN.PartII.continuousToL2
      (selectedProbability hm hs X : Measure X) (v i)))
    (hdim : Fintype.card ι = Module.finrank ℝ (spectralCutoff (selectedProbability hm hs X : Measure X) η))
    (p : ENNReal) [Fact (1 ≤ p)] (hpfin : p ≠ ⊤) (hp2 : 2 ≤ p)
    [StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs X : Measure X))] :
    ∃ (g : ι → C(C, ℝ)) (gs : ℕ → ι → C(C, ℝ)),
      (∀ i, (g i).comp ⟨C.limitMap, C.limit_isometry.continuous⟩ = v i) ∧
      (∀ i, Tendsto (fun n ↦ gs n i) atTop (𝓝 (g i))) ∧
      Tendsto (fun n ↦ unitNormError
        (coordinateLpNorm (selectedProbability hm hs (Xs n) : Measure (Xs n)) p
          (fun i ↦ (gs n i).comp ⟨C.seqMap n, (C.seq_isometry n).continuous⟩))
        (coordinateLpNorm (selectedProbability hm hs X : Measure X) p v)) atTop (𝓝 0) ∧
      ∀ (R : ∀ n, PaperN.Shared.Correspondence (Xs n) X),
        Tendsto (fun n ↦ ⨆ z : (R n).rel,
          dist (C.seqMap n z.val.1) (C.limitMap z.val.2)) atTop (𝓝 0) →
        Tendsto (fun n ↦ ⨆ z : (R n).rel,
          ‖coordinateLpMinimizer (selectedProbability hm hs (Xs n) : Measure (Xs n)) p
            (fun i ↦ (gs n i).comp ⟨C.seqMap n, (C.seq_isometry n).continuous⟩)
            (ContinuousMap.toLp p (selectedProbability hm hs (Xs n) : Measure (Xs n)) ℝ
              (PaperN.PartII.distanceProfile z.val.1)) -
            coordinateLpMinimizer (selectedProbability hm hs X : Measure X) p v
              (ContinuousMap.toLp p (selectedProbability hm hs X : Measure X) ℝ
                (PaperN.PartII.distanceProfile z.val.2))‖) atTop (𝓝 0) := by
  obtain ⟨g, gs, hext, hconv, hu⟩ := selected_spectral_coordinates_uniform_nearby
    hm hp hs C   hf   hH η hη hpos hneg v hv ho hdim p hpfin hp2
  refine ⟨g, gs, hext, hconv, ?_, ?_⟩
  · have hn := coordinateLpNorm_unitNormError_tendsto _ _
      (selectedProbability_tendsto hm hp hs Xs X C hH) p hpfin gs g hconv
    have hms (n : ℕ) (a : EuclideanSpace ℝ ι) := coordinateLpNorm_map
      (selectedProbability hm hs (Xs n))
      (⟨C.seqMap n, (C.seq_isometry n).continuous⟩ : C(Xs n, C)) p hpfin (gs n) a
    have hm0 (a : EuclideanSpace ℝ ι) := coordinateLpNorm_map
      (selectedProbability hm hs X)
      (⟨C.limitMap, C.limit_isometry.continuous⟩ : C(X, C)) p hpfin g a
    simpa only [unitNormError, hms, hm0, hext] using hn
  · intro R hRseq
    have ht := nearby_pair_sup_tendsto (fun n ↦ (R n).rel)
      (fun n z ↦ C.seqMap n z.val.1) (fun n z ↦ C.limitMap z.val.2)
      (fun n z ↦ coordinateLpMinimizer
        (selectedProbability hm hs (Xs n) : Measure (Xs n)) p
        (fun i ↦ (gs n i).comp ⟨C.seqMap n, (C.seq_isometry n).continuous⟩)
        (ContinuousMap.toLp p (selectedProbability hm hs (Xs n) : Measure (Xs n)) ℝ
          (PaperN.PartII.distanceProfile z.val.1)))
      (fun _ z ↦ coordinateLpMinimizer (selectedProbability hm hs X : Measure X) p v
        (ContinuousMap.toLp p (selectedProbability hm hs X : Measure X) ℝ
          (PaperN.PartII.distanceProfile z.val.2))) hRseq ?_
    · simpa only [dist_eq_norm] using ht
    · intro r hr ε hε
      filter_upwards [hu r hr ε hε] with n hn
      intro z hz
      exact hn z.val.1 z.val.2 hz

end PaperN.PartII.AmbientKernel
