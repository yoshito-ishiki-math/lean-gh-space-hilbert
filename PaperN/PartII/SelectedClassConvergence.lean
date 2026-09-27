import PaperN.PartII.SubspaceModelConvergence

namespace PaperN.PartII.AmbientKernel
open MeasureTheory Filter PaperN.PartI ComplexKernel
open scoped Topology

noncomputable def selectedSpectralCoordinateClass
    (hm : GHPMetricInput.{0}) (hs : InvariantFiberLawSelectionStatement hm)
    (hf : CompactEigenvalueFinitenessInput.{0}) (X : MeasuredCompact.{0})
    (η : ℝ) (hη : 0 < η) (p : ENNReal) [Fact (1 ≤ p)]
    [StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs X : Measure X))]
    (n : ℕ) (hd : n = Module.finrank ℝ
      (spectralCutoff (selectedProbability hm hs X : Measure X) η)) :
    NormedCoordinateClass X (EuclideanSpace ℝ (Fin n)) := by
  let μ := selectedProbability hm hs X
  letI : (μ : Measure X).IsOpenPosMeasure :=
    openPos_of_support_eq_univ _ (selectedProbability_fullSupport_invariant hm hs X).1
  letI := realCutoff_finiteDimensional (μ : Measure X) hf η hη
  letI : FiniteDimensional ℝ (spectralCutoff (μ : Measure X) η) :=
    (spectralCutoffEquiv (μ : Measure X) hη).symm.finiteDimensional
  exact subspaceCoordinateClass (μ : Measure X) _ p n hd

/-- Selected spectral classes admit representatives converging simultaneously
in both model errors. Common rank and Lp strict convexity remain explicit. -/
theorem selected_spectral_class_representatives_converge
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm)
    {Xs : ℕ → MeasuredCompact.{0}} {X : MeasuredCompact.{0}} (C : CommonRealization Xs X)

    (hf : CompactEigenvalueFinitenessInput.{0})
     (hH : C.HausdorffConverges) (η : ℝ) (hη : 0 < η)
    (hpos : (η : ℂ) ∈ resolventSet ℂ
      (ComplexKernel.distanceOperator (selectedProbability hm hs X : Measure X)))
    (hneg : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ
      (ComplexKernel.distanceOperator (selectedProbability hm hs X : Measure X)))
    (n : ℕ) [NeZero n]
    (hd : n = Module.finrank ℝ (spectralCutoff (selectedProbability hm hs X : Measure X) η))
    (hds : ∀ k, n = Module.finrank ℝ
      (spectralCutoff (selectedProbability hm hs (Xs k) : Measure (Xs k)) η))
    (p : ENNReal) [Fact (1 ≤ p)] (hpfin : p ≠ ⊤) (hp2 : 2 ≤ p)
    [StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs X : Measure X))]
    [∀ k, StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs (Xs k) : Measure (Xs k)))] :
    ∃ a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin n)),
      ∃ as : ∀ k, NormedCoordinatePair (Xs k) (EuclideanSpace ℝ (Fin n)),
        Quotient.mk _ a = selectedSpectralCoordinateClass hm hs hf X η hη p n hd ∧
        (∀ k, Quotient.mk _ (as k) =
          selectedSpectralCoordinateClass hm hs hf (Xs k) η hη p n (hds k)) ∧
        Tendsto (fun k ↦ unitNormError (as k).norm a.norm) atTop (𝓝 0) ∧
        ∀ R : ∀ k, PaperN.Shared.Correspondence (Xs k) X,
          Tendsto (fun k ↦ ⨆ z : (R k).rel,
            dist (C.seqMap k z.val.1) (C.limitMap z.val.2)) atTop (𝓝 0) →
          Tendsto (fun k ↦ coordinateError (R k) (as k).coordinates a.coordinates) atTop (𝓝 0) := by
  let μ := selectedProbability hm hs X
  let μs := fun k ↦ selectedProbability hm hs (Xs k)
  let S := spectralCutoff (μ : Measure X) η
  let Ss := fun k ↦ spectralCutoff (μs k : Measure (Xs k)) η
  letI : (μ : Measure X).IsOpenPosMeasure :=
    openPos_of_support_eq_univ _ (selectedProbability_fullSupport_invariant hm hs X).1
  letI : ∀ k, (μs k : Measure (Xs k)).IsOpenPosMeasure := fun k ↦
    openPos_of_support_eq_univ _ (selectedProbability_fullSupport_invariant hm hs (Xs k)).1
  letI := realCutoff_finiteDimensional (μ : Measure X) hf η hη
  letI : FiniteDimensional ℝ S :=
    (spectralCutoffEquiv (μ : Measure X) hη).symm.finiteDimensional
  letI : ∀ k, FiniteDimensional ℝ (Ss k) := fun k ↦ by
    letI := realCutoff_finiteDimensional (μs k : Measure (Xs k)) hf η hη
    exact (spectralCutoffEquiv (μs k : Measure (Xs k)) hη).symm.finiteDimensional
  let b := subspaceOrthonormalBasis (μ : Measure X) S n hd
  let v := fun i ↦ (b i : C(X, ℝ))
  have ho := subspaceOrthonormalBasis_orthonormal (μ : Measure X) S n hd
  obtain ⟨g, gs, hext, hconv, hgood⟩ := selected_spectral_basis_extensions
    hm hp hs C   hf   hH η hη hpos hneg v (fun i ↦ (b i).property) ho
    (by simpa using hd)
  have h := exists_convergent_subspace_representatives (fun k ↦ Xs k) μs μ Ss S
    C.seqMap C.seq_isometry C.limitMap C.limit_isometry
    (selectedProbability_tendsto hm hp hs Xs X C hH) p hpfin hp2 n hds hd gs g hconv
    (fun i ↦ by rw [hext]; exact (b i).property)
    (by simpa only [hext] using ho) (hgood.mono (fun _ h ↦ ⟨h.1, h.2.1⟩))
  exact h

end PaperN.PartII.AmbientKernel
