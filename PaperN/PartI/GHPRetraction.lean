import PaperN.PartI.GHSection
import PaperN.PartI.GHPRetractionStatements

namespace PaperN.PartI
open GromovHausdorff Set Topology

/-- A continuous section has a continuous retraction onto its actual range. -/
theorem exists_range_retraction {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (s : C(A, B)) (p : C(B, A)) (h : Function.LeftInverse p s) :
    ∃ r : C(B, range s), ∀ x : range s, r x.val = x := by
  refine ⟨⟨fun x ↦ ⟨s (p x), ⟨p x, rfl⟩⟩, (s.continuous.comp p.continuous).subtype_mk _⟩, ?_⟩
  intro x
  apply Subtype.ext
  obtain ⟨a, ha⟩ := x.property
  change s (p x.val) = x.val
  rw [← ha, h a]

/-- Restriction of the same retraction to every subspace containing the section image. -/
theorem exists_subspace_range_retraction {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (s : C(A, B)) (p : C(B, A)) (h : Function.LeftInverse p s)
    (S : Set B) (hS : range s ⊆ S) :
    ∃ r : C(S, range s), ∀ x : range s, r ⟨x.val, hS x.property⟩ = x := by
  obtain ⟨r, hr⟩ := exists_range_retraction s p h
  exact ⟨r.comp ⟨Subtype.val, continuous_subtype_val⟩, hr⟩

/-- A section is homeomorphic to its range, with the given projection as inverse. -/
noncomputable def sectionRangeHomeomorph {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (s : C(A, B)) (p : C(B, A)) (h : Function.LeftInverse p s) : A ≃ₜ range s where
  toFun a := ⟨s a, ⟨a, rfl⟩⟩
  invFun x := p x.val
  left_inv := h
  right_inv x := by
    apply Subtype.ext
    obtain ⟨a, ha⟩ := x.property
    change s (p x.val) = x.val
    rw [← ha, h a]
  continuous_toFun := s.continuous.subtype_mk _
  continuous_invFun := p.continuous.comp continuous_subtype_val

/-- The selected GH section is an embedding, has invariant full-support image, and
its image is a retract of the whole measured space and every containing subspace. -/
theorem ghpRetraction_of_selection (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hg : GHCommonEmbeddingInput.{0}) (hs : InvariantFiberLawSelectionStatement hm) :
    GHPRetractionStatement hm := by
  letI := hm.metricSpace
  let s : C(GHSpace, MeasuredGHSpace.{0}) :=
    ⟨selectedGHSection hm hs, continuous_selectedGHSection hm hp hg hs⟩
  let p : C(MeasuredGHSpace.{0}, GHSpace) :=
    ⟨MeasuredGHSpace.forget, (ghpForgetLipschitz_spec hm).continuous⟩
  have h : Function.LeftInverse p s := forget_selectedGHSection hm hs
  refine ⟨s, h, h.isEmbedding p.continuous s.continuous, ?_,
    ⟨sectionRangeHomeomorph s p h⟩, exists_range_retraction s p h,
    exists_subspace_range_retraction s p h⟩
  intro q
  refine ⟨selectedGHSection_invariant hm hs q, ?_⟩
  exact (selectedProbability_fullSupport_invariant hm hs (ghRepresentative q)).1

/-- The retract corollary follows from the same six explicit cited inputs as M1/M2/M3. -/
theorem ghpRetraction_spec (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hc : GHPCommonEmbeddingInput.{0}) (hg : GHCommonEmbeddingInput.{0})
    (ha : ProbabilityApproximationInput.{0}) (hv : InvariantValovInput hm hp hc) :
    GHPRetractionStatement hm :=
  ghpRetraction_of_selection hm hp hg (invariantFiberLawSelection_spec hm hp hc hg ha hv)
end PaperN.PartI
