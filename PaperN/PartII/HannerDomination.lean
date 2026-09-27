import PaperN.PartII.AbsoluteNeighborhoodRetract
import PaperN.PartII.GlobalARDomination

namespace PaperN.PartII
open TopologicalSpace GromovHausdorff PaperN.PartI

/-- Small homotopy domination in a fixed compatible metric. -/
def HasSmallANRDomination (X : Type) [MetricSpace X] : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (Y : Type) (m : MetricSpace Y),
    letI := m
    SeparableSpace Y ∧ IsAbsoluteNeighborhoodRetract.{0,0} Y ∧
    ∃ f : X → Y, ∃ g : Y → X, Continuous f ∧ Continuous g ∧
      ∃ H : X → Set.Icc (0 : ℝ) 1 → X,
        Continuous (fun p : X × Set.Icc (0 : ℝ) 1 ↦ H p.1 p.2) ∧
        (∀ x, H x ⟨0, by constructor <;> norm_num⟩ = x) ∧
        (∀ x, H x ⟨1, by constructor <;> norm_num⟩ = g (f x)) ∧
        (∀ x, Metric.diam (Set.range (H x)) < ε)

/-- General input: Hanner 1951, Theorem 7.2(b), in the separable metric category. -/
def HannerDominationInput : Prop :=
  ∀ (X : Type) [MetricSpace X] [SeparableSpace X], HasSmallANRDomination X →
    IsSeparableAbsoluteNeighborhoodRetract.{0,0} X

/-- General input: Hanner 1952, Theorem 13.4, enlargement of the ambient category. -/
def HannerANRCategoryInput : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [SeparableSpace X],
    IsSeparableAbsoluteNeighborhoodRetract.{0,0} X → IsAbsoluteNeighborhoodRetract.{0,0} X

namespace AmbientKernel
/-- The constructed variable-error domination supplies Hanner's constant-error hypothesis. -/
theorem ghSpace_hasSmallANRDomination
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm) (hg : GHCommonEmbeddingInput.{0})
    (hk : DistanceKernelSpectralInput.{0})

    (hf : CompactEigenvalueFinitenessInput.{0})

    (hH : EquivariantHyperspaceARInput) (hO : OrbitARInput) :
    HasSmallANRDomination GHSpace := by
  intro ε hε
  obtain ⟨n, _, hsep, hAR, f, hfc, hgc, e, _, _, _, H, hc, h0, h1, _, _, hd⟩ :=
    exists_AR_domination hm hp hs hg hk   hf   hH hO
      (fun _ ↦ ε) continuous_const (fun _ ↦ hε)
  exact ⟨SphereOrbit.Space n, SphereOrbit.metricSpace n, hsep,
    hAR.isAbsoluteNeighborhoodRetract, f, SphereOrbit.realization n,
    hfc, hgc, H, hc, h0, h1, hd⟩

/-- GH space is an ANR in all metrizable Type-0 ambient spaces under the general inputs. -/
theorem ghSpace_absoluteNeighborhoodRetract
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm) (hg : GHCommonEmbeddingInput.{0})
    (hk : DistanceKernelSpectralInput.{0})

    (hf : CompactEigenvalueFinitenessInput.{0})

    (hH : EquivariantHyperspaceARInput) (hO : OrbitARInput)
    (hD : HannerDominationInput) (hA : HannerANRCategoryInput) :
    IsAbsoluteNeighborhoodRetract.{0,0} GHSpace :=
  hA GHSpace (hD GHSpace
    (ghSpace_hasSmallANRDomination hm hp hs hg hk   hf   hH hO))

end AmbientKernel
end PaperN.PartII
