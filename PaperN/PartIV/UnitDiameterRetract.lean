import PaperN.PartIV.UnitDiameterContraction
import PaperN.PartIV.HilbertRecognition

namespace PaperN.PartIV
open PaperN.PartI PaperN.PartII GromovHausdorff Set TopologicalSpace

/-- A retract of an open subset of an AE is an ANE, directly from extension definitions. -/
theorem ane_of_open_retract {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    [MetrizableSpace Z] (hX : IsAbsoluteExtensor.{_,0} X)
    (U : Set X) (hU : IsOpen U) (e : Z → U) (he : Continuous e)
    (r : U → Z) (hr : Continuous r) (hre : Function.LeftInverse r e) :
    IsAbsoluteNeighborhoodExtensor.{_,0} Z := by
  refine ⟨inferInstance, ?_⟩
  intro Y _ _ A hA f hf
  obtain ⟨F,hF,hFe⟩ := hX.2 Y A hA (fun a ↦ (e (f a)).val)
    (he.comp hf).subtype_val
  have hsub : A ⊆ F ⁻¹' U := by
    intro y hy
    change F y ∈ U
    rw [hFe ⟨y,hy⟩]
    exact (e (f ⟨y,hy⟩)).property
  let G : (F ⁻¹' U) → U := fun y ↦ ⟨F y.val, y.property⟩
  have hG : Continuous G := (hF.comp continuous_subtype_val).subtype_mk _
  refine ⟨F ⁻¹' U, hU.preimage hF, hsub, r ∘ G, hr.comp hG, ?_⟩
  intro a ha
  have heq : G ⟨a.val,ha⟩ = e (f a) := Subtype.ext (hFe a)
  change r (G ⟨a.val,ha⟩) = f a
  rw [heq, hre]

/-- Normalization transfers neighborhood extension to the diameter-one subspace. -/
theorem unitDiameter_absoluteNeighborhoodExtensor
    (hX : IsAbsoluteExtensor.{0,0} GHSpace) :
    IsAbsoluteNeighborhoodExtensor.{0,0} UnitDiameterSpace := by
  let e : UnitDiameterSpace → {q : GHSpace // 0 < ghDiameter q} :=
    fun q ↦ ⟨q.val, by rw [q.property]; norm_num⟩
  exact ane_of_open_retract hX _ positiveDiameter_isOpen e
    (continuous_subtype_val.subtype_mk _) diameterNormalize diameterNormalize_continuous
    diameterNormalize_retract

/-- The proved contraction upgrades the neighborhood extension property to absolute extension. -/
theorem unitDiameter_absoluteExtensor
    (hX : IsAbsoluteExtensor.{0,0} GHSpace) (hK : ContractibleANEToAEInput) :
    IsAbsoluteExtensor.{0,0} UnitDiameterSpace := by
  letI : Nonempty UnitDiameterSpace := unitDiameter_nonempty
  letI : ContractibleSpace UnitDiameterSpace := unitDiameter_contractible
  exact hK UnitDiameterSpace (unitDiameter_absoluteNeighborhoodExtensor hX)

/-- The diameter-one subspace is an AR under the same extension inputs. -/
theorem unitDiameter_absoluteRetract
    (hX : IsAbsoluteExtensor.{0,0} GHSpace) (hK : ContractibleANEToAEInput) :
    IsAbsoluteRetract.{0,0} UnitDiameterSpace :=
  (unitDiameter_absoluteExtensor hX hK).isAbsoluteRetract

/-- Recognition gives the unit-diameter Hilbert-space corollary. -/
theorem unitDiameter_homeomorphic_hilbert_of_absoluteExtensor
    (hX : IsAbsoluteExtensor.{0,0} GHSpace) (hK : ContractibleANEToAEInput)
    (hg : GHCommonEmbeddingInput.{0}) (hT : TorunczykRecognitionInput) :
    Nonempty (UnitDiameterSpace ≃ₜ RealHilbertSpace) := by
  letI : Nonempty UnitDiameterSpace := unitDiameter_nonempty
  letI : TopologicalSpace.SeparableSpace UnitDiameterSpace :=
    inferInstanceAs (TopologicalSpace.SeparableSpace {q : GHSpace // ghDiameter q = 1})
  exact (hT UnitDiameterSpace (unitDiameter_absoluteRetract hX hK)).mpr
    (unitDiameter_hilbertCubeDiscreteApproximation hg)

/-- The unit-diameter corollary with all source inputs explicitly exposed. -/
theorem unitDiameter_homeomorphic_hilbert
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm) (hg : GHCommonEmbeddingInput.{0})
    (hk : DistanceKernelSpectralInput.{0})

    (hf : CompactEigenvalueFinitenessInput.{0})

    (hH : EquivariantHyperspaceARInput) (hO : OrbitARInput)
    (hD : HannerDominationInput) (hA : HannerANRCategoryInput)
     (hK : ContractibleANEToAEInput)
    (hT : TorunczykRecognitionInput) : Nonempty (UnitDiameterSpace ≃ₜ RealHilbertSpace) :=
  unitDiameter_homeomorphic_hilbert_of_absoluteExtensor
    (AmbientKernel.ghSpace_absoluteExtensor hm hp hs hg hk   hf   hH hO hD hA  hK)
    hK hg hT

end PaperN.PartIV
