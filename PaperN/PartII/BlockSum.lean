import PaperN.PartII.DualActionContinuity
import Mathlib.Analysis.Normed.Lp.lpSpace

namespace PaperN.PartII
variable {I : Type*} {B : I → Type*} [∀ i, NormedAddCommGroup (B i)] [∀ i, NormedSpace ℝ (B i)]

omit [∀ i, NormedSpace ℝ (B i)] in
/-- The l1 block norm is the sum of the individual block norms. -/
theorem blockSum_norm (f : lp B 1) : ‖f‖ = ∑' i, ‖f i‖ := by
  simpa using lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal) f

/-- Coordinatewise isometric equivalences preserve l1 summability. -/
theorem blockSum_mem (U : ∀ i, B i ≃ₗᵢ[ℝ] B i) (f : lp B 1) :
    Memℓp (fun i ↦ U i (f i)) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ENNReal).toReal)]
  simpa only [LinearIsometryEquiv.norm_map] using (lp.memℓp f).summable
    (by norm_num : 0 < (1 : ENNReal).toReal)

/-- Blockwise isometries act linearly and isometrically on the l1 sum. -/
noncomputable def blockSumAction (U : ∀ i, B i ≃ₗᵢ[ℝ] B i) : lp B 1 →ₗᵢ[ℝ] lp B 1 where
  toFun f := ⟨fun i ↦ U i (f i), blockSum_mem U f⟩
  map_add' f g := by apply Subtype.ext; funext i; exact (U i).map_add _ _
  map_smul' c f := by apply Subtype.ext; funext i; exact (U i).map_smul c _
  norm_map' f := by
    rw [blockSum_norm, blockSum_norm]
    exact tsum_congr (fun i ↦ (U i).norm_map (f i))

/-- The blockwise action is surjective, by applying inverse maps in every block. -/
theorem blockSumAction_surjective (U : ∀ i, B i ≃ₗᵢ[ℝ] B i) :
    Function.Surjective (blockSumAction U) := by
  intro f
  refine ⟨blockSumAction (fun i ↦ (U i).symm) f, ?_⟩
  apply Subtype.ext
  funext i
  exact (U i).apply_symm_apply (f i)

@[simp] theorem blockSumAction_refl (f : lp B 1) :
    blockSumAction (fun i ↦ LinearIsometryEquiv.refl ℝ (B i)) f = f := by
  apply Subtype.ext
  rfl

theorem blockSumAction_trans (U V : ∀ i, B i ≃ₗᵢ[ℝ] B i) (f : lp B 1) :
    blockSumAction (fun i ↦ (U i).trans (V i)) f = blockSumAction V (blockSumAction U f) := by
  apply Subtype.ext
  rfl

/-- The corresponding surjective linear isometry of the full l1 space. -/
noncomputable def blockSumActionEquiv (U : ∀ i, B i ≃ₗᵢ[ℝ] B i) : lp B 1 ≃ₗᵢ[ℝ] lp B 1 :=
  LinearIsometryEquiv.ofSurjective (blockSumAction U) (blockSumAction_surjective U)

/-- The fixed block space used by the global local-model construction. -/
noncomputable abbrev SphereBlockSum (n : ℕ → ℕ) :=
  lp (fun i ↦ C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n i))) 1, ℝ)) 1

/-- The countable sphere-function block sum is a Banach space. -/
theorem sphereBlockSum_complete (n : ℕ → ℕ) : CompleteSpace (SphereBlockSum n) := inferInstance

/-- Orthogonal changes in all coordinate blocks induce a surjective linear isometry. -/
noncomputable def sphereBlockSumAction (n : ℕ → ℕ)
    (U : ∀ i, EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n i))) :
    SphereBlockSum n ≃ₗᵢ[ℝ] SphereBlockSum n :=
  blockSumActionEquiv (fun i ↦ orthogonalSphereActionEquiv (U i))

end PaperN.PartII
