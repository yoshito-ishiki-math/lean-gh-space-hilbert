import PaperN.PartII.CompactSetRealization

namespace PaperN.PartII
variable {I : Type*} [DecidableEq I] {B : I → Type*}
    [∀ i, NormedAddCommGroup (B i)] [∀ i, NormedSpace ℝ (B i)]

/-- Finite weighted assembly of block vectors into the l1 space. -/
noncomputable def finiteBlockFeature (s : Finset I) (w : I → ℝ) (f : ∀ i, B i) : lp B 1 :=
  ∑ i ∈ s, lp.single 1 i (w i • f i)

/-- The norm of the assembled feature is the weighted sum of block norms. -/
theorem finiteBlockFeature_norm (s : Finset I) (w : I → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (f : ∀ i, B i) : ‖finiteBlockFeature s w f‖ = ∑ i ∈ s, w i * ‖f i‖ := by
  have h := lp.norm_sum_single (by norm_num : 0 < (1 : ENNReal).toReal) (fun i ↦ w i • f i) s
  simp only [ENNReal.toReal_one, Real.rpow_one] at h
  rw [finiteBlockFeature, h]
  apply Finset.sum_congr rfl
  intro i hi
  rw [norm_smul, Real.norm_of_nonneg (hw i hi)]

/-- The assembled distance is the weighted sum of the block distances. -/
theorem finiteBlockFeature_dist (s : Finset I) (w : I → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (f g : ∀ i, B i) :
    dist (finiteBlockFeature s w f) (finiteBlockFeature s w g) = ∑ i ∈ s, w i * dist (f i) (g i) := by
  rw [dist_eq_norm]
  have h : finiteBlockFeature s w f - finiteBlockFeature s w g =
      finiteBlockFeature s w (fun i ↦ f i - g i) := by
    simp only [finiteBlockFeature, ← Finset.sum_sub_distrib, ← lp.single_sub, smul_sub]
  rw [h, finiteBlockFeature_norm s w hw]
  simp only [dist_eq_norm]

/-- Finite assembly commutes with independent orthogonal/isometric changes of blocks. -/
theorem finiteBlockFeature_equivariant (s : Finset I) (w : I → ℝ)
    (U : ∀ i, B i ≃ₗᵢ[ℝ] B i) (f : ∀ i, B i) :
    blockSumAction U (finiteBlockFeature s w f) = finiteBlockFeature s w (fun i ↦ U i (f i)) := by
  simp only [finiteBlockFeature, map_sum, blockSumAction_single, map_smul]

/-- With continuous block maps, finite weighted assembly is continuous. -/
theorem continuous_finiteBlockFeature {X : Type*} [TopologicalSpace X]
    (s : Finset I) (w : I → ℝ) (f : ∀ i, X → B i) (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun x ↦ finiteBlockFeature s w (fun i ↦ f i x)) := by
  apply continuous_finsetSum
  intro i hi
  exact (lp.singleContinuousLinearMap (𝕜 := ℝ) (E := B) (p := 1) i).continuous.comp
    ((hf i hi).const_smul (w i))

/-- The actual sphere-feature distance is the sum of weighted local norm distances. -/
theorem finiteDualFeature_dist (n : ℕ → ℕ) (s : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (p : ∀ i, Seminorm ℝ (EuclideanSpace ℝ (Fin (n i))))
    (hp : ∀ i v, p i v = 0 → v = 0)
    (x y : ∀ i, EuclideanSpace ℝ (Fin (n i))) :
    dist (finiteBlockFeature s w (fun i ↦ coordinateDualEmbedding (p i) (hp i) (x i)))
      (finiteBlockFeature s w (fun i ↦ coordinateDualEmbedding (p i) (hp i) (y i))) =
      ∑ i ∈ s, w i * p i (x i - y i) := by
  rw [finiteBlockFeature_dist s w hw]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dist_eq_norm, coordinateDualEmbedding_norm_sub]

/-- Finite assembly remains continuous when both weights and block vectors vary. -/
theorem continuous_finiteBlockFeature_variable {X : Type*} [TopologicalSpace X]
    (s : Finset I) (w : I → X → ℝ) (f : ∀ i, X → B i)
    (hw : ∀ i ∈ s, Continuous (w i)) (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun x ↦ finiteBlockFeature s (fun i ↦ w i x) (fun i ↦ f i x)) := by
  apply continuous_finsetSum
  intro i hi
  exact (lp.singleContinuousLinearMap (𝕜 := ℝ) (E := B) (p := 1) i).continuous.comp
    ((hw i hi).smul (hf i hi))

/-- Adding indices with zero weight does not change the feature. -/
theorem finiteBlockFeature_eq_of_subset (s t : Finset I) (hst : s ⊆ t)
    (w : I → ℝ) (f : ∀ i, B i) (hw : ∀ i ∈ t, i ∉ s → w i = 0) :
    finiteBlockFeature s w f = finiteBlockFeature t w f := by
  apply Finset.sum_subset hst
  intro i hit his
  simp [hw i hit his]

end PaperN.PartII
