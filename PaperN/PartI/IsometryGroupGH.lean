import PaperN.PartI.IsometryGroup
import PaperN.PartI.Anisometry
import PaperN.Shared.Statements
import Mathlib.Topology.Perfect
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable

namespace PaperN.PartI
open GromovHausdorff PaperN.Shared
variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MetricSpace Y] [CompactSpace Y]

/-- Conjugation transports the entire group, including its uniform metric. -/
noncomputable def isometryGroupConjugacy (e : X ≃ᵢ Y) : (X ≃ᵢ X) ≃ᵢ (Y ≃ᵢ Y) where
  toFun g := e.symm.trans (g.trans e)
  invFun g := e.trans (g.trans e.symm)
  left_inv g := by ext x; simp
  right_inv g := by ext x; simp
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro g h
    apply le_antisymm
    · apply (isometryGroup_dist_le dist_nonneg).2
      intro y
      change dist (e (g (e.symm y))) (e (h (e.symm y))) ≤ dist g h
      rw [e.dist_eq]
      exact isometryGroup_apply_dist_le g h _
    · apply (isometryGroup_dist_le dist_nonneg).2
      intro x
      have ht := isometryGroup_apply_dist_le
        (e.symm.trans (g.trans e)) (e.symm.trans (h.trans e)) (e x)
      simpa only [IsometryEquiv.trans_apply, IsometryEquiv.symm_apply_apply, e.dist_eq] using ht

/-- The GH class of the compact full isometry group with uniform distance. -/
noncomputable def isometryGroupGH (q : GHSpace) : GHSpace :=
  toGHSpace (q.Rep ≃ᵢ q.Rep)

/-- This construction agrees with any concrete representative, in any universe. -/
theorem isometryGroupGH_toGHSpace (X : Type*) [MetricSpace X] [CompactSpace X] [Nonempty X] :
    isometryGroupGH (toGHSpace X) = toGHSpace (X ≃ᵢ X) := by
  obtain ⟨e⟩ := toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp
    (GHSpace.toGHSpace_rep (toGHSpace X))
  exact toGHSpace_eq_toGHSpace_iff_isometryEquiv.mpr ⟨isometryGroupConjugacy e⟩

/-- Exactly the rigid spaces are sent to the one-point GH class. -/
theorem isometryGroupGH_eq_point_iff (q : GHSpace) :
    isometryGroupGH q = pointGH ↔ Subsingleton (q.Rep ≃ᵢ q.Rep) := by
  constructor
  · intro h
    obtain ⟨e⟩ := toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp h
    exact e.injective.subsingleton
  · intro h
    letI := h
    letI : Unique (q.Rep ≃ᵢ q.Rep) := ⟨⟨IsometryEquiv.refl _⟩, fun _ ↦ Subsingleton.elim _ _⟩
    let e : (q.Rep ≃ᵢ q.Rep) ≃ᵢ Unit := {
      toEquiv := Equiv.ofUnique _ _
      isometry_toFun := fun a b ↦ by simp [Subsingleton.elim a b] }
    exact toGHSpace_eq_toGHSpace_iff_isometryEquiv.mpr ⟨e⟩

/-- Given density of rigid compacta, every symmetric point is a discontinuity point. -/
theorem isometryGroupGH_not_continuousAt
    (hd : Dense {q : GHSpace | Subsingleton (q.Rep ≃ᵢ q.Rep)})
    {q : GHSpace} (hq : ¬ Subsingleton (q.Rep ≃ᵢ q.Rep)) :
    ¬ ContinuousAt isometryGroupGH q := by
  apply not_continuousAt_of_dense_constant hd
    (fun x hx ↦ (isometryGroupGH_eq_point_iff x).mpr hx)
  exact fun h ↦ hq ((isometryGroupGH_eq_point_iff q).mp h)

/-- Nonempty perfect metric spaces are infinite; finite metric spaces are discrete. -/
theorem infinite_of_perfect_metric (X : Type*) [MetricSpace X] [Nonempty X]
    [PerfectSpace X] : Infinite X := by
  by_contra h
  haveI : Finite X := not_infinite_iff_finite.mp h
  let x : X := Classical.choice inferInstance
  have hn := PerfectSpace.not_isolated x
  exact hn.ne (by simp [nhdsWithin, nhds_discrete, Filter.inf_principal_eq_bot])

/-- The two residual conclusions cited from Rouyer arXiv v1, Theorems 2 and 4.
An explicit source input, not a global axiom or an asserted inhabitant. -/
structure RouyerGenericInput : Prop where
  anisometric : {q : GHSpace | TotallyAnisometric q.Rep} ∈ residual GHSpace
  perfect : {q : GHSpace | PerfectSpace q.Rep} ∈ residual GHSpace

/-- Rouyer's two residual properties imply density of rigid compact spaces. -/
theorem dense_rigid_of_rouyer (hR : RouyerGenericInput) :
    Dense {q : GHSpace | Subsingleton (q.Rep ≃ᵢ q.Rep)} := by
  apply (dense_of_mem_residual (Filter.inter_mem hR.anisometric hR.perfect)).mono
  intro q hq
  letI : PerfectSpace q.Rep := hq.2
  letI := infinite_of_perfect_metric q.Rep
  exact subsingleton_isometryEquiv_of_infinite_totallyAnisometric hq.1

/-- Every point with nontrivial isometry group is a discontinuity point. -/
theorem isometryGroupGH_discontinuous_of_rouyer (hR : RouyerGenericInput)
    {q : GHSpace} (hq : ¬ Subsingleton (q.Rep ≃ᵢ q.Rep)) :
    ¬ ContinuousAt isometryGroupGH q :=
  isometryGroupGH_not_continuousAt (dense_rigid_of_rouyer hR) hq

end PaperN.PartI
