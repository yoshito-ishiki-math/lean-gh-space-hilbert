import PaperN.PartIV.HilbertCubeApproximation
import PaperN.PartI.GHCommonEmbeddingProof

namespace PaperN.PartIV
open PaperN.PartI GromovHausdorff Set

/-- The compact-domain discrete approximation theorem has no remaining literature inputs. -/
theorem discreteApproximation_main
    {D : ℕ → Type*} [∀ j, TopologicalSpace (D j)] [∀ j, CompactSpace (D j)]
    (f : ∀ j, D j → GHSpace) (hf : ∀ j, Continuous (f j))
    {I : Type*} [Nonempty I] (U : I → Set GHSpace)
    (ho : ∀ i, IsOpen (U i)) (hc : ∀ q, ∃ i, q ∈ U i) :
    ∃ g : ∀ j, D j → GHSpace, (∀ j, Continuous (g j)) ∧
      (∀ j x, ∃ i, f j x ∈ U i ∧ g j x ∈ U i) ∧
      IsDiscreteFamily (fun j ↦ range (g j)) :=
  exists_discrete_approximations f hf U ho hc ghCommonEmbeddingInput_proved

/-- The exact Hilbert-cube approximation premise of recognition, proved without inputs. -/
theorem hilbertCubeDiscreteApproximation_main :
    HasHilbertCubeDiscreteApproximation GHSpace :=
  ghSpace_hilbertCubeDiscreteApproximation ghCommonEmbeddingInput_proved
end PaperN.PartIV
