import PaperN.PartII.SelectedCoefficientConvergence
import PaperN.PartII.LpNormTransport

namespace PaperN.PartII.AmbientKernel
open MeasureTheory Filter PaperN.PartI ComplexKernel
open scoped Topology

theorem selected_spectral_coordinates_and_norms_tendsto
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm)
    {Xs : ℕ → MeasuredCompact.{0}} {X : MeasuredCompact.{0}} (C : CommonRealization Xs X)

    (hf : CompactEigenvalueFinitenessInput.{0})
     (hH : C.HausdorffConverges) (η : ℝ) (hη : 0 < η)
    (hpos : (η : ℂ) ∈ resolventSet ℂ
      (ComplexKernel.distanceOperator (selectedProbability hm hs X : Measure X)))
    (hneg : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ
      (ComplexKernel.distanceOperator (selectedProbability hm hs X : Measure X)))
    {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → C(X, ℝ))
    (hv : ∀ i, v i ∈ spectralCutoff (selectedProbability hm hs X : Measure X) η)
    (ho : Orthonormal ℝ (fun i ↦ PaperN.PartII.continuousToL2
      (selectedProbability hm hs X : Measure X) (v i)))
    (hdim : Fintype.card ι = Module.finrank ℝ (spectralCutoff (selectedProbability hm hs X : Measure X) η))
    (p : ENNReal) [Fact (1 ≤ p)] (hpfin : p ≠ ⊤) (hp2 : 2 ≤ p)
    [StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs X : Measure X))] :
    ∃ (g : ι → C(C, ℝ)) (gs : ℕ → ι → C(C, ℝ)),
      (∀ i, (g i).comp ⟨C.limitMap, C.limit_isometry.continuous⟩ = v i) ∧
      (∀ i, Tendsto (fun n ↦ gs n i) atTop (𝓝 (g i))) ∧
      (∀ᶠ n in atTop, ∀ i,
        (gs n i).comp ⟨C.seqMap n, (C.seq_isometry n).continuous⟩ ∈
          spectralCutoff (selectedProbability hm hs (Xs n) : Measure (Xs n)) η) ∧
      (∀ (K : Set (EuclideanSpace ℝ ι)), IsCompact K →
        TendstoUniformly
          (fun n (a : K) ↦ coordinateLpNorm
            (selectedProbability hm hs (Xs n) : Measure (Xs n)) p
            (fun i ↦ (gs n i).comp ⟨C.seqMap n, (C.seq_isometry n).continuous⟩) a)
          (fun a : K ↦ coordinateLpNorm (selectedProbability hm hs X : Measure X) p v a)
          atTop) ∧
      ∀ (xs : ∀ n, Xs n) (x : X),
        Tendsto (fun n ↦ C.seqMap n (xs n)) atTop (𝓝 (C.limitMap x)) →
        Tendsto (fun n ↦ coordinateLpMinimizer
          (selectedProbability hm hs (Xs n) : Measure (Xs n)) p
          (fun i ↦ (gs n i).comp ⟨C.seqMap n, (C.seq_isometry n).continuous⟩)
          (ContinuousMap.toLp p (selectedProbability hm hs (Xs n) : Measure (Xs n)) ℝ
            (PaperN.PartII.distanceProfile (xs n)))) atTop
          (𝓝 (coordinateLpMinimizer (selectedProbability hm hs X : Measure X) p v
            (ContinuousMap.toLp p (selectedProbability hm hs X : Measure X) ℝ
              (PaperN.PartII.distanceProfile x)))) := by
  obtain ⟨g, gs, hext, hconv, hmem, hcoeff⟩ := selected_spectral_coefficients_tendsto
    hm hp hs C   hf   hH η hη hpos hneg v hv ho hdim p hpfin hp2
  refine ⟨g, gs, hext, hconv, hmem, ?_, hcoeff⟩
  intro K hK
  have hn := intrinsic_coordinateLpNorm_uniform_on_compact (fun n ↦ ↥(Xs n))
    (fun n ↦ selectedProbability hm hs (Xs n)) (selectedProbability hm hs X)
    (fun n ↦ ⟨C.seqMap n, (C.seq_isometry n).continuous⟩)
    ⟨C.limitMap, C.limit_isometry.continuous⟩
    (selectedProbability_tendsto hm hp hs Xs X C hH) p hpfin gs g hconv K hK
  simpa only [hext] using hn

end PaperN.PartII.AmbientKernel

namespace PaperN.PartII
open MeasureTheory Filter Topology

/-- Intrinsic norm values converge also along moving coefficient differences. -/
theorem intrinsic_coordinateLpNorm_sub_tendsto
    {Z X ι : Type*} (Xs : ℕ → Type*)
    [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [∀ n, MetricSpace (Xs n)] [∀ n, CompactSpace (Xs n)]
    [∀ n, MeasurableSpace (Xs n)] [∀ n, BorelSpace (Xs n)] [Fintype ι]
    (μs : ∀ n, ProbabilityMeasure (Xs n)) (μ : ProbabilityMeasure X)
    (es : ∀ n, C(Xs n, Z)) (e : C(X, Z))
    (hμ : Tendsto (fun n ↦ (μs n).map (es n).continuous.measurable.aemeasurable)
      atTop (𝓝 (μ.map e.continuous.measurable.aemeasurable)))
    (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (vs : ℕ → ι → C(Z, ℝ)) (v : ι → C(Z, ℝ))
    (hv : ∀ i, Tendsto (fun n ↦ vs n i) atTop (𝓝 (v i)))
    (as bs : ℕ → EuclideanSpace ℝ ι) (a b : EuclideanSpace ℝ ι)
    (ha : Tendsto as atTop (𝓝 a)) (hb : Tendsto bs atTop (𝓝 b)) :
    Tendsto (fun n ↦ coordinateLpNorm (μs n : Measure (Xs n)) p
      (fun i ↦ (vs n i).comp (es n)) (as n - bs n)) atTop
      (𝓝 (coordinateLpNorm (μ : Measure X) p (fun i ↦ (v i).comp e) (a - b))) := by
  have h := coordinateLpNorm_tendsto _ _ hμ p hp vs v hv _ _ (ha.sub hb)
  simpa only [coordinateLpNorm_map _ _ p hp] using h

end PaperN.PartII
