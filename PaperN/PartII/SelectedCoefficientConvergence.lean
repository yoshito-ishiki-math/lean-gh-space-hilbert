import PaperN.PartII.SelectedSpectralBasis
import PaperN.PartII.OrthonormalFamilySpan

namespace PaperN.PartII.AmbientKernel
open MeasureTheory Filter PaperN.PartI ComplexKernel
open scoped Topology

theorem selected_spectral_coefficients_tendsto
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
  obtain ⟨g, gs, hext, hconv, hb⟩ := selected_spectral_basis_extensions
    hm hp hs C   hf   hH η hη hpos hneg v hv ho hdim
  letI : (selectedProbability hm hs X : Measure X).IsOpenPosMeasure :=
    openPos_of_support_eq_univ _ (selectedProbability_fullSupport_invariant hm hs X).1
  refine ⟨g, gs, hext, hconv, hb.mono (fun _ hn ↦ hn.1), ?_⟩
  intro xs x hx
  have hli : LinearIndependent ℝ (fun i ↦ (g i).comp
      ⟨C.limitMap, C.limit_isometry.continuous⟩) := by
    simp only [hext]
    exact LinearIndependent.of_comp (continuousToL2
      (selectedProbability hm hs X : Measure X)).toLinearMap ho.linearIndependent
  have ht := embedded_orthonormal_family_coefficient_tendsto (fun n ↦ ↥(Xs n))
    (fun n ↦ selectedProbability hm hs (Xs n)) (selectedProbability hm hs X)
    C.seqMap C.seq_isometry C.limitMap C.limit_isometry
    (selectedProbability_tendsto hm hp hs Xs X C hH) p hpfin gs g hconv hli xs x hx hp2
    (hb.mono (fun _ hn ↦ hn.2.1))
  simpa only [hext] using ht

end PaperN.PartII.AmbientKernel
