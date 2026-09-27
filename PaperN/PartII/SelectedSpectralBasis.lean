import PaperN.PartII.NormalizedRestriction

namespace PaperN.PartII.AmbientKernel
open MeasureTheory Filter PaperN.PartI ComplexKernel
open scoped Topology

theorem selected_spectral_basis_extensions
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
    (hdim : Fintype.card ι = Module.finrank ℝ (spectralCutoff (selectedProbability hm hs X : Measure X) η)) :
    ∃ (g : ι → C(C, ℝ)) (gs : ℕ → ι → C(C, ℝ)),
      (∀ i, (g i).comp ⟨C.limitMap, C.limit_isometry.continuous⟩ = v i) ∧
      (∀ i, Tendsto (fun n ↦ gs n i) atTop (𝓝 (g i))) ∧
      ∀ᶠ n in atTop,
        (∀ i, (gs n i).comp ⟨C.seqMap n, (C.seq_isometry n).continuous⟩ ∈
          spectralCutoff (selectedProbability hm hs (Xs n) : Measure (Xs n)) η) ∧
        Orthonormal ℝ (fun i ↦ PaperN.PartII.continuousToL2
          (selectedProbability hm hs (Xs n) : Measure (Xs n))
          ((gs n i).comp ⟨C.seqMap n, (C.seq_isometry n).continuous⟩)) ∧
        ∃ b : ι → spectralCutoff (selectedProbability hm hs (Xs n) : Measure (Xs n)) η,
          (∀ i, (b i : C(Xs n, ℝ)) = (gs n i).comp ⟨C.seqMap n, (C.seq_isometry n).continuous⟩) ∧
          Submodule.span ℝ (Set.range b) = ⊤ := by
  let e : C(X, C) := ⟨C.limitMap, C.limit_isometry.continuous⟩
  let es : ∀ n, C(Xs n, C) := fun n ↦ ⟨C.seqMap n, (C.seq_isometry n).continuous⟩
  let μ := selectedProbability hm hs X
  let μs := fun n ↦ selectedProbability hm hs (Xs n)
  let ν := μ.map e
  let νs := fun n ↦ (μs n).map (es n)
  let P := cutoffContourOperator (selectedLimitOperator hm hs C) (Metric.diam (Set.univ : Set C)) η
  let Ps := fun n ↦ cutoffContourOperator (selectedSequenceOperator hm hs C n)
    (Metric.diam (Set.univ : Set C)) η
  have hall := spectralProjections_spec hm hp hs C   hf   hH η hη hpos hneg
  letI : (μ : Measure X).IsOpenPosMeasure :=
    openPos_of_support_eq_univ _ (selectedProbability_fullSupport_invariant hm hs X).1
  obtain ⟨g, hext, hfix, hconv⟩ := exists_convergent_projected_extensions e (μ : Measure X)
    C.limit_isometry η hη Ps P hall.1 hall.2.2 v hv
  let ws := fun n i ↦ realProjectedFunction (Ps n) (g i)
  have hν : Tendsto νs atTop (𝓝 ν) := selectedProbability_tendsto hm hp hs Xs X C hH
  have hgram : continuousGram ν g = 1 := continuousGram_map_eq_one e μ g v hext ho
  let gs := fun n ↦ normalizeContinuousFamily (νs n) (ws n)
  refine ⟨g, gs, hext, ?_, ?_⟩
  · exact fun i ↦ normalizeContinuousFamily_tendsto νs ν hν ws g hconv hgram i
  · filter_upwards [hall.2.1, continuousGram_eventually_posDef νs ν hν ws g hconv hgram] with n hn hg
    letI : (μs n : Measure (Xs n)).IsOpenPosMeasure :=
      openPos_of_support_eq_univ _ (selectedProbability_fullSupport_invariant hm hs (Xs n)).1
    have hmem : ∀ i, (gs n i).comp (es n) ∈ spectralCutoff (μs n : Measure (Xs n)) η := by
      intro i
      apply normalize_restrict_mem (es n) (νs n) (ws n)
      intro j
      exact realProjectedFunction_mem_cutoff (es n) (μs n : Measure (Xs n)) (C.seq_isometry n)
        η hη (Ps n) hn.2.2.2 (g j)
    have horth := normalized_restrictions_orthonormal (es n) (μs n) (ws n) hg
    refine ⟨hmem, horth, ?_⟩
    let b : ι → spectralCutoff (μs n : Measure (Xs n)) η := fun i ↦ ⟨(gs n i).comp (es n), hmem i⟩
    letI := realCutoff_finiteDimensional (μs n : Measure (Xs n)) hf η hη
    letI : FiniteDimensional ℝ (spectralCutoff (μs n : Measure (Xs n)) η) :=
      (spectralCutoffEquiv (μs n : Measure (Xs n)) hη).symm.finiteDimensional
    refine ⟨b, fun _ ↦ rfl, ?_⟩
    apply orthonormal_continuousFamily_span (μs n : Measure (Xs n)) _ b horth
    exact hdim.trans hn.2.2.1.symm

end PaperN.PartII.AmbientKernel
