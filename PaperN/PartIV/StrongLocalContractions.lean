import PaperN.PartIV.HilbertRecognition
import PaperN.PartII.BanachContinua

namespace PaperN.PartIV
open Set Metric GromovHausdorff PaperN.PartI PaperN.PartII

/-- An open neighborhood basis with contractions that remain inside and fix the center. -/
def HasStrongLocalContractions (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ (x : X) (U : Set X), IsOpen U → x ∈ U →
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ H : V × Icc (0 : ℝ) 1 → X, Continuous H ∧
        (∀ y t, H (y,t) ∈ V) ∧
        (∀ y, H (y,⟨0,by norm_num⟩) = y.val) ∧
        (∀ y, H (y,⟨1,by norm_num⟩) = x) ∧
        (∀ (hx : x ∈ V) t, H (⟨x,hx⟩,t) = x)

/-- Pulling back convex balls gives strong local contractions under any normed-space homeomorphism. -/
theorem strongLocalContractions_of_homeomorph
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : X ≃ₜ E) : HasStrongLocalContractions X := by
  intro x U hU hx
  have ho : IsOpen (h.symm ⁻¹' U) := hU.preimage h.symm.continuous
  have hm : h x ∈ h.symm ⁻¹' U := by simpa using hx
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hm)
  let V := h ⁻¹' ball (h x) r
  have hxV : x ∈ V := mem_ball_self hr
  have hVU : V ⊆ U := by
    intro y hy
    have := hsub hy
    simpa using this
  let K (p : V × Icc (0 : ℝ) 1) : E :=
    (1-p.2.val) • h p.1.val + p.2.val • h x
  have hK : Continuous K := by
    have ht : Continuous (fun p : V × Icc (0 : ℝ) 1 ↦ p.2.val) :=
      continuous_subtype_val.comp continuous_snd
    exact ((continuous_const.sub ht).smul
      (h.continuous.comp (continuous_subtype_val.comp continuous_fst))).add
      (ht.smul continuous_const)
  have hmem (y : V) (t : Icc (0 : ℝ) 1) : K (y,t) ∈ ball (h x) r :=
    (convex_ball (h x) r) y.property (mem_ball_self hr)
      (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
  refine ⟨V, isOpen_ball.preimage h.continuous, hxV, hVU,
    fun p ↦ h.symm (K p), h.symm.continuous.comp hK, ?_, ?_, ?_, ?_⟩
  · intro y t
    change h (h.symm (K (y,t))) ∈ ball (h x) r
    simpa only [h.apply_symm_apply] using hmem y t
  · intro y
    simp [K]
  · intro y
    simp [K]
  · intro hx t
    dsimp [K]
    rw [← add_smul]
    simp

/-- The main homeomorphism implies the strong local contraction corollary. -/
theorem ghSpace_strongLocalContractions_of_homeomorph
    (h : Nonempty (GHSpace ≃ₜ RealHilbertSpace)) : HasStrongLocalContractions GHSpace := by
  obtain ⟨e⟩ := h
  exact strongLocalContractions_of_homeomorph e

/-- Strong local contractions under the main theorem's complete explicit input boundary. -/
theorem ghSpace_strongLocalContractions
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm) (hg : GHCommonEmbeddingInput.{0})
    (hk : DistanceKernelSpectralInput.{0})

    (hf : CompactEigenvalueFinitenessInput.{0})

    (hH : EquivariantHyperspaceARInput) (hO : OrbitARInput)
    (hD : HannerDominationInput) (hA : HannerANRCategoryInput)
     (hK : ContractibleANEToAEInput)
    (hT : TorunczykRecognitionInput) : HasStrongLocalContractions GHSpace :=
  ghSpace_strongLocalContractions_of_homeomorph
    (ghSpace_homeomorphic_hilbert hm hp hs hg hk   hf   hH hO hD hA  hK hT)

end PaperN.PartIV
