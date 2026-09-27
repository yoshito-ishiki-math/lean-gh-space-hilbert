import PaperN.PartI.CommonBaseGluing

set_option backward.isDefEq.respectTransparency false

namespace PaperN.PartI.BasedAmbient
open Metric GromovHausdorff Set Filter
open scoped Topology
universe u
variable (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
variable (Xs : ℕ → Type u) [∀ n, MetricSpace (Xs n)]
  [∀ n, CompactSpace (Xs n)] [∀ n, Nonempty (Xs n)]

/-- All finite fixed-base gluings in one metric carrier. -/
abbrev JointCarrier := Metric.InductiveLimit (towerStep_isometry (X := X) Xs)

noncomputable def jointBase : X → JointCarrier X Xs :=
  toInductiveLimit (towerStep_isometry (X := X) Xs) 0 ∘ (tower Xs 0).base

noncomputable def jointMap (n : ℕ) : Xs n → JointCarrier X Xs :=
  toInductiveLimit (towerStep_isometry (X := X) Xs) (n + 1) ∘ (tower Xs n).newMap (Xs n)

theorem jointBase_at (n : ℕ) :
    toInductiveLimit (towerStep_isometry (X := X) Xs) n ∘ (tower Xs n).base =
      jointBase X Xs := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← towerStep_base, ← Function.comp_assoc, toInductiveLimit_commute, ih]

theorem jointBase_isometry : Isometry (jointBase X Xs) :=
  (toInductiveLimit_isometry _ _).comp (tower Xs 0).base_isometry

theorem jointMap_isometry (n : ℕ) : Isometry (jointMap X Xs n) :=
  (toInductiveLimit_isometry _ _).comp ((tower Xs n).newMap_isometry (Xs n))

/-- All GH distances to the fixed base are simultaneously realized. -/
theorem joint_hausdorffDist (n : ℕ) :
    hausdorffDist (range (jointBase X Xs)) (range (jointMap X Xs n)) = ghDist X (Xs n) := by
  rw [← jointBase_at X Xs (n + 1)]
  change hausdorffDist (range (toInductiveLimit (towerStep_isometry (X := X) Xs) (n + 1) ∘ ((tower Xs n).attach (Xs n)).base))
    (range (toInductiveLimit (towerStep_isometry (X := X) Xs) (n + 1) ∘ (tower Xs n).newMap (Xs n))) = _
  rw [range_comp, range_comp, hausdorffDist_image (toInductiveLimit_isometry _ _)]
  exact (tower Xs n).attach_hausdorffDist (Xs n)

/-- GH convergence becomes Hausdorff convergence in the single joint carrier. -/
theorem joint_hausdorffConverges
    (h : Tendsto (fun n ↦ toGHSpace (Xs n)) atTop (𝓝 (toGHSpace X))) :
    Tendsto (fun n ↦ hausdorffDist (range (jointMap X Xs n)) (range (jointBase X Xs)))
      atTop (𝓝 0) := by
  have hd := tendsto_iff_dist_tendsto_zero.mp h
  convert hd using 1
  funext n
  rw [hausdorffDist_comm, joint_hausdorffDist]
  exact dist_comm _ _
end PaperN.PartI.BasedAmbient
