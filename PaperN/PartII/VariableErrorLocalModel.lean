import PaperN.PartII.LocalModelGHContinuity

namespace PaperN.PartII
open PaperN.PartI GromovHausdorff Set

namespace LocalModel
variable {X₀ : MeasuredCompact.{0}} {τ : ℝ}

/-- Shrink a local model to lie below a continuous variable error control. -/
noncomputable def shrinkBelow (M : LocalModel X₀ τ) (ε : GHSpace → ℝ)
    (hε : Continuous ε) (hc : M.error (toGHSpace X₀) < ε (toGHSpace X₀)) :
    LocalModel X₀ τ :=
  M.restrict (M.domain ∩ (fun q ↦ M.error q - ε q) ⁻¹' Iio 0)
    ((M.error_continuous.sub hε.continuousOn).isOpen_inter_preimage M.domain_open isOpen_Iio)
    ⟨M.center_mem, sub_neg.mpr hc⟩ inter_subset_left

/-- The variable strict error bound holds throughout the shrunken neighborhood. -/
theorem shrinkBelow_error_lt (M : LocalModel X₀ τ) (ε : GHSpace → ℝ)
    (hε : Continuous ε) (hc : M.error (toGHSpace X₀) < ε (toGHSpace X₀))
    (q : GHSpace) (hq : q ∈ (M.shrinkBelow ε hε hc).domain) :
    (M.shrinkBelow ε hε hc).error q < ε q := sub_neg.mp hq.2

end LocalModel

namespace AmbientKernel
/-- At every GH point there is a continuous local approximation below the prescribed
positive continuous control on its entire open domain. -/
theorem exists_variable_error_localModel
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm) (hg : GHCommonEmbeddingInput.{0})
    (hk : DistanceKernelSpectralInput.{0})

    (hf : CompactEigenvalueFinitenessInput.{0})

    (ε : GHSpace → ℝ) (hε : Continuous ε) (hpos : ∀ q, 0 < ε q) (q : GHSpace) :
    ∃ M : LocalModel (ghRepresentative q) (ε q),
      q ∈ M.domain ∧ Continuous M.ghMap ∧ ∀ r ∈ M.domain, M.error r < ε r := by
  obtain ⟨M⟩ := exists_localModel hm hp hs hg hk   hf
    (ghRepresentative q) (ε q) (hpos q)
  have hc : M.error (toGHSpace (ghRepresentative q)) < ε (toGHSpace (ghRepresentative q)) := by
    simpa only [ghRepresentative_class] using M.center_error
  refine ⟨M.shrinkBelow ε hε hc, ?_, (M.shrinkBelow ε hε hc).continuous_ghMap hg, ?_⟩
  · simpa only [ghRepresentative_class] using (M.shrinkBelow ε hε hc).center_mem
  · exact M.shrinkBelow_error_lt ε hε hc

/-- The local models form an open cover with variable error control, ready for a
subordinate partition of unity. -/
theorem exists_variable_error_model_cover
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm) (hg : GHCommonEmbeddingInput.{0})
    (hk : DistanceKernelSpectralInput.{0})

    (hf : CompactEigenvalueFinitenessInput.{0})

    (ε : GHSpace → ℝ) (hε : Continuous ε) (hpos : ∀ q, 0 < ε q) :
    ∃ M : ∀ q : GHSpace, LocalModel (ghRepresentative q) (ε q),
      (∀ q, IsOpen (M q).domain) ∧ (⋃ q, (M q).domain) = univ ∧
      (∀ q, q ∈ (M q).domain) ∧ (∀ q, Continuous (M q).ghMap) ∧
      (∀ q r, r ∈ (M q).domain → (M q).error r < ε r) := by
  choose M hcenter hcont herr using
    exists_variable_error_localModel hm hp hs hg hk   hf   ε hε hpos
  refine ⟨M, fun q ↦ (M q).domain_open, ?_, hcenter, hcont, herr⟩
  apply Set.eq_univ_of_forall
  intro q
  exact Set.mem_iUnion.mpr ⟨q, hcenter q⟩

end AmbientKernel
end PaperN.PartII
