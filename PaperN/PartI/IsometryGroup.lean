import PaperN.PartI.IsometryGroupDefs
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Tactic

namespace PaperN.PartI
open Set Metric Topology
open scoped BoundedContinuousFunction
variable {X : Type*} [MetricSpace X] [CompactSpace X]

lemma isometryGroup_dist_le {g h : X ≃ᵢ X} {r : ℝ} (hr : 0 ≤ r) :
    dist g h ≤ r ↔ ∀ x, dist (g x) (h x) ≤ r :=
  BoundedContinuousFunction.dist_le hr

lemma isometryGroup_apply_dist_le (g h : X ≃ᵢ X) (x : X) :
    dist (g x) (h x) ≤ dist g h :=
  BoundedContinuousFunction.dist_coe_le_dist (f := isometryBCF g) (g := isometryBCF h) x

lemma isometryGroup_inv_dist_le (g h : X ≃ᵢ X) : dist g⁻¹ h⁻¹ ≤ dist g h := by
  apply (isometryGroup_dist_le dist_nonneg).2
  intro x
  rw [← g.dist_eq, IsometryEquiv.apply_inv_self]
  have he := isometryGroup_apply_dist_le g h (h⁻¹ x)
  simpa only [IsometryEquiv.apply_inv_self, dist_comm] using he

lemma isometryGroup_inv_dist (g h : X ≃ᵢ X) : dist g⁻¹ h⁻¹ = dist g h := by
  apply le_antisymm (isometryGroup_inv_dist_le g h)
  simpa using isometryGroup_inv_dist_le g⁻¹ h⁻¹

lemma isometryGroup_mul_dist (g h g' h' : X ≃ᵢ X) :
    dist (g * h) (g' * h') ≤ dist g g' + dist h h' := by
  apply (isometryGroup_dist_le (add_nonneg dist_nonneg dist_nonneg)).2
  intro x
  change dist (g (h x)) (g' (h' x)) ≤ _
  calc
    _ ≤ dist (g (h x)) (g' (h x)) + dist (g' (h x)) (g' (h' x)) := dist_triangle _ _ _
    _ ≤ dist g g' + dist h h' := by
      rw [g'.dist_eq]
      exact add_le_add (isometryGroup_apply_dist_le g g' _) (isometryGroup_apply_dist_le h h' x)

instance isometryGroupTopological : IsTopologicalGroup (X ≃ᵢ X) where
  continuous_mul := by
    apply (show LipschitzWith 2 (fun p : (X ≃ᵢ X) × (X ≃ᵢ X) ↦ p.1 * p.2) from ?_).continuous
    apply LipschitzWith.of_dist_le_mul
    intro p q
    have h := isometryGroup_mul_dist p.1 p.2 q.1 q.2
    have h1 : dist p.1 q.1 ≤ dist p q := le_max_left _ _
    have h2 : dist p.2 q.2 ≤ dist p q := le_max_right _ _
    norm_num only [NNReal.coe_ofNat]
    linarith
  continuous_inv := (Isometry.of_dist_eq isometryGroup_inv_dist).continuous

/-- Isometric self-embeddings, without surjectivity, form a compact set of uniform maps. -/
lemma isCompact_isometricMaps : IsCompact {f : X →ᵇ X | Isometry f} := by
  apply BoundedContinuousFunction.arzela_ascoli₁
  · have heq : {f : X →ᵇ X | Isometry f} =
        ⋂ x : X, ⋂ y : X, {f : X →ᵇ X | dist (f x) (f y) = dist x y} := by
      ext f
      simp only [mem_setOf_eq, mem_iInter, isometry_iff_dist_eq]
    rw [heq]
    exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦
      isClosed_eq (by fun_prop) continuous_const
  · intro x
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, fun y hy f ↦ ?_⟩
    simpa [f.property.dist_eq, dist_comm] using hy

private abbrev IsometricMaps (X : Type*) [MetricSpace X] [CompactSpace X] :=
  {f : X →ᵇ X // Isometry f}

private instance compactIsometricMaps : CompactSpace (IsometricMaps X) :=
  isCompact_iff_compactSpace.1 isCompact_isometricMaps

private def InversePair (p : IsometricMaps X × IsometricMaps X) : Prop :=
  (∀ x, p.1.val (p.2.val x) = x) ∧ ∀ x, p.2.val (p.1.val x) = x

private lemma isClosed_inversePairs : IsClosed {p : IsometricMaps X × IsometricMaps X | InversePair p} := by
  have heq : {p : IsometricMaps X × IsometricMaps X | InversePair p} =
      (⋂ x : X, {p : IsometricMaps X × IsometricMaps X | p.1.val (p.2.val x) = x}) ∩
      (⋂ x : X, {p : IsometricMaps X × IsometricMaps X | p.2.val (p.1.val x) = x}) := by
    ext p
    simp [InversePair]
  rw [heq]
  apply IsClosed.inter <;> apply isClosed_iInter <;> intro x <;>
    exact isClosed_eq (by fun_prop) continuous_const

private noncomputable def pairToIsometry
    (p : {p : IsometricMaps X × IsometricMaps X // InversePair p}) : X ≃ᵢ X where
  toFun := p.val.1.val
  invFun := p.val.2.val
  left_inv := p.property.2
  right_inv := p.property.1
  isometry_toFun := p.val.1.property

/-- Compactness is obtained from mutually inverse pairs, without assuming that
isometric self-embeddings are surjective. -/
instance isometryGroupCompact : CompactSpace (X ≃ᵢ X) := by
  let P := {p : IsometricMaps X × IsometricMaps X // InversePair p}
  haveI : CompactSpace P := isCompact_iff_compactSpace.1 isClosed_inversePairs.isCompact
  have hc : Continuous (pairToIsometry (X := X)) := by
    apply isometry_isometryBCF.isEmbedding.continuous_iff.2
    change Continuous (fun p : P ↦ p.val.1.val)
    fun_prop
  have hs : Function.Surjective (pairToIsometry (X := X)) := by
    intro g
    let p : P := ⟨(⟨isometryBCF g, g.isometry⟩, ⟨isometryBCF g⁻¹, g.symm.isometry⟩),
      ⟨g.apply_symm_apply, g.symm_apply_apply⟩⟩
    exact ⟨p, by ext x; rfl⟩
  exact hs.compactSpace hc

/-- Joint evaluation is continuous for the uniform group topology. -/
lemma continuous_isometryGroup_eval : Continuous (fun p : (X ≃ᵢ X) × X ↦ p.1 p.2) := by
  have hc := (isometry_isometryBCF (X := X)).continuous
  change Continuous (fun p : (X ≃ᵢ X) × X ↦ isometryBCF p.1 p.2)
  fun_prop

end PaperN.PartI
