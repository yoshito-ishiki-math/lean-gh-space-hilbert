import PaperN.PartII.SelectedSpectralBasis
import PaperN.PartII.OrthonormalFamilySpan
import PaperN.PartII.UniformRelationConvergence

namespace PaperN.PartII
open MeasureTheory Filter Topology
variable {Z X ι : Type*} (Xs : ℕ → Type*)
  [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [∀ n, MetricSpace (Xs n)] [∀ n, CompactSpace (Xs n)]
  [∀ n, MeasurableSpace (Xs n)] [∀ n, BorelSpace (Xs n)] [Fintype ι]

theorem embedded_coefficient_uniform_nearby
    (μs : ∀ n, ProbabilityMeasure (Xs n)) (μ : ProbabilityMeasure X)
    [(μ : Measure X).IsOpenPosMeasure]
    (es : ∀ n, Xs n → Z) (hes : ∀ n, Isometry (es n))
    (e : X → Z) (he : Isometry e)
    (hμ : Tendsto (fun n ↦ (μs n).map (hes n).continuous.measurable.aemeasurable)
      atTop (𝓝 (μ.map he.continuous.measurable.aemeasurable)))
    (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [StrictConvexSpace ℝ (Lp ℝ p (μ : Measure X))]
    (vs : ℕ → ι → C(Z, ℝ)) (v : ι → C(Z, ℝ))
    (hv : ∀ i, Tendsto (fun n ↦ vs n i) atTop (𝓝 (v i)))
    (hli : LinearIndependent ℝ (fun i ↦ (v i).comp ⟨e, he.continuous⟩))
    (hp2 : 2 ≤ p)
    (ho : ∀ᶠ n in atTop, Orthonormal ℝ (fun i ↦
      ContinuousMap.toLp 2 (μs n : Measure (Xs n)) ℝ
        ((vs n i).comp ⟨es n, (hes n).continuous⟩)))
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ (x : Xs n) (y : X),
      dist (es n x) (e y) ≤ r n →
      dist (coordinateLpMinimizer (μs n : Measure (Xs n)) p
        (fun i ↦ (vs n i).comp ⟨es n, (hes n).continuous⟩)
        (ContinuousMap.toLp p (μs n : Measure (Xs n)) ℝ (distanceProfile x)))
        (coordinateLpMinimizer (μ : Measure X) p
          (fun i ↦ (v i).comp ⟨e, he.continuous⟩)
          (ContinuousMap.toLp p (μ : Measure X) ℝ (distanceProfile y))) < ε := by
  apply uniform_nearby_of_sequential Xs es e he.continuous _ _
    (bestApproximationCoordinates (μ : Measure X) p _ hli).continuous r hr
  intro φ hφ xs x hx
  exact embedded_orthonormal_family_coefficient_tendsto (fun n ↦ Xs (φ n))
    (fun n ↦ μs (φ n)) μ (fun n ↦ es (φ n)) (fun n ↦ hes (φ n)) e he
    (hμ.comp hφ) p hp (fun n ↦ vs (φ n)) v (fun i ↦ (hv i).comp hφ)
    hli xs x hx hp2 (hφ.eventually ho)

end PaperN.PartII

namespace PaperN.PartII.AmbientKernel
open MeasureTheory Filter PaperN.PartI ComplexKernel
open scoped Topology

theorem selected_spectral_coordinates_uniform_nearby
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
      ∀ (r : ℕ → ℝ), Tendsto r atTop (𝓝 0) →
        ∀ ε > 0, ∀ᶠ n in atTop, ∀ (x : Xs n) (y : X),
          dist (C.seqMap n x) (C.limitMap y) ≤ r n →
          dist (coordinateLpMinimizer
            (selectedProbability hm hs (Xs n) : Measure (Xs n)) p
            (fun i ↦ (gs n i).comp ⟨C.seqMap n, (C.seq_isometry n).continuous⟩)
            (ContinuousMap.toLp p (selectedProbability hm hs (Xs n) : Measure (Xs n)) ℝ
              (PaperN.PartII.distanceProfile x)))
            (coordinateLpMinimizer (selectedProbability hm hs X : Measure X) p v
              (ContinuousMap.toLp p (selectedProbability hm hs X : Measure X) ℝ
                (PaperN.PartII.distanceProfile y))) < ε := by
  obtain ⟨g, gs, hext, hconv, hb⟩ := selected_spectral_basis_extensions
    hm hp hs C   hf   hH η hη hpos hneg v hv ho hdim
  letI : (selectedProbability hm hs X : Measure X).IsOpenPosMeasure :=
    openPos_of_support_eq_univ _ (selectedProbability_fullSupport_invariant hm hs X).1
  refine ⟨g, gs, hext, hconv, ?_⟩
  intro r hr
  have hli : LinearIndependent ℝ (fun i ↦ (g i).comp
      ⟨C.limitMap, C.limit_isometry.continuous⟩) := by
    simp only [hext]
    exact LinearIndependent.of_comp (continuousToL2
      (selectedProbability hm hs X : Measure X)).toLinearMap ho.linearIndependent
  have ht := embedded_coefficient_uniform_nearby (fun n ↦ ↥(Xs n))
    (fun n ↦ selectedProbability hm hs (Xs n)) (selectedProbability hm hs X)
    C.seqMap C.seq_isometry C.limitMap C.limit_isometry
    (selectedProbability_tendsto hm hp hs Xs X C hH) p hpfin gs g hconv hli hp2
    (hb.mono (fun _ hn ↦ hn.2.1)) r hr
  simpa only [hext] using ht

end PaperN.PartII.AmbientKernel
