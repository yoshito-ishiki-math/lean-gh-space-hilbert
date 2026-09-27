import PaperN.PartII.SelectedSpectralBasis
import PaperN.PartII.FiniteFamilyConvergence

namespace PaperN.PartII.AmbientKernel
open MeasureTheory Filter PaperN.PartI ComplexKernel
open scoped Topology

theorem spectralContinuity_spec
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
      (∀ (_ : Nonempty ι), Tendsto (fun n ↦ ⨆ i, ‖gs n i - g i‖) atTop (𝓝 0)) ∧
      (∀ (_ : Nonempty ι) (A : ℕ → Type) (_ : ∀ n, Nonempty (A n))
        (x y : ∀ n, A n → C),
        Tendsto (fun n ↦ ⨆ a, dist (x n a) (y n a)) atTop (𝓝 0) →
        Tendsto (fun n ↦ ⨆ p : ι × A n, |gs n p.1 (x n p.2) - g p.1 (y n p.2)|)
          atTop (𝓝 0)) ∧
      ∀ᶠ n in atTop,
        (η : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator
          (selectedProbability hm hs (Xs n) : Measure (Xs n))) ∧
        ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator
          (selectedProbability hm hs (Xs n) : Measure (Xs n))) ∧
        Module.finrank ℝ (spectralCutoff (selectedProbability hm hs (Xs n) : Measure (Xs n)) η) =
          Module.finrank ℝ (spectralCutoff (selectedProbability hm hs X : Measure X) η) ∧
        (∀ i, (gs n i).comp ⟨C.seqMap n, (C.seq_isometry n).continuous⟩ ∈
          spectralCutoff (selectedProbability hm hs (Xs n) : Measure (Xs n)) η) ∧
        Orthonormal ℝ (fun i ↦ PaperN.PartII.continuousToL2
          (selectedProbability hm hs (Xs n) : Measure (Xs n))
          ((gs n i).comp ⟨C.seqMap n, (C.seq_isometry n).continuous⟩)) ∧
        ∃ b : ι → spectralCutoff (selectedProbability hm hs (Xs n) : Measure (Xs n)) η,
          (∀ i, (b i : C(Xs n, ℝ)) = (gs n i).comp ⟨C.seqMap n, (C.seq_isometry n).continuous⟩) ∧
          Submodule.span ℝ (Set.range b) = ⊤ := by
  obtain ⟨g, gs, hext, hconv, hb⟩ := selected_spectral_basis_extensions
    hm hp hs C   hf   hH η hη hpos hneg v hv ho hdim
  refine ⟨g, gs, hext, hconv, ?_, ?_, ?_⟩
  · intro hi
    letI := hi
    exact finite_family_norm_tendsto gs g hconv
  · intro hi A hA x y hxy
    letI := hi
    letI := hA
    apply nearby_family_sup_tendsto gs g hconv x y
      (fun n ↦ ⨆ a, dist (x n a) (y n a)) hxy
    intro n a
    have hb : BddAbove (Set.range (fun a ↦ dist (x n a) (y n a))) := by
      refine ⟨Metric.diam (Set.univ : Set C), ?_⟩
      rintro _ ⟨b, rfl⟩
      exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (Set.mem_univ _) (Set.mem_univ _)
    exact le_ciSup hb a
  · have hall := spectralProjections_spec hm hp hs C   hf   hH η hη hpos hneg
    filter_upwards [hall.2.1, hb] with n hn hbn
    exact ⟨hn.1, hn.2.1, hn.2.2.1, hbn⟩

end PaperN.PartII.AmbientKernel
