import PaperN.PartI.LiftInputs

namespace PaperN.PartI
open Metric GromovHausdorff Set
universe u

/-- A metric ambient together with the fixed limit carrier embedded in it. -/
structure BasedAmbient (X : Type u) [MetricSpace X] where
  Carrier : Type u
  metric : MetricSpace Carrier
  base : X → Carrier
  base_isometry : Isometry base
attribute [instance] BasedAmbient.metric

namespace BasedAmbient
variable {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X]

/-- Adjoin one optimal coupling along the fixed base carrier. -/
noncomputable def attach (A : BasedAmbient X) (Y : Type u)
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y] : BasedAmbient X where
  Carrier := GlueSpace A.base_isometry (isometry_optimalGHInjl X Y)
  metric := inferInstance
  base := toGlueL A.base_isometry (isometry_optimalGHInjl X Y) ∘ A.base
  base_isometry := (toGlueL_isometry _ _).comp A.base_isometry

noncomputable def inclusion (A : BasedAmbient X) (Y : Type u)
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y] : A.Carrier → (A.attach Y).Carrier :=
  toGlueL A.base_isometry (isometry_optimalGHInjl X Y)

noncomputable def newMap (A : BasedAmbient X) (Y : Type u)
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y] : Y → (A.attach Y).Carrier :=
  toGlueR A.base_isometry (isometry_optimalGHInjl X Y) ∘ optimalGHInjr X Y

theorem inclusion_isometry (A : BasedAmbient X) (Y : Type u)
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y] : Isometry (A.inclusion Y) :=
  toGlueL_isometry _ _

theorem newMap_isometry (A : BasedAmbient X) (Y : Type u)
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y] : Isometry (A.newMap Y) :=
  (toGlueR_isometry _ _).comp (isometry_optimalGHInjr X Y)

/-- No error is accumulated when adjoining another carrier along the same limit. -/
theorem attach_hausdorffDist (A : BasedAmbient X) (Y : Type u)
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y] :
    hausdorffDist (range (A.attach Y).base) (range (A.newMap Y)) = ghDist X Y := by
  change hausdorffDist (range (toGlueL A.base_isometry (isometry_optimalGHInjl X Y) ∘ A.base))
    (range (toGlueR A.base_isometry (isometry_optimalGHInjl X Y) ∘ optimalGHInjr X Y)) = _
  rw [toGlue_commute, range_comp, range_comp,
    hausdorffDist_image (toGlueR_isometry _ _), hausdorffDist_optimal]

/-- Successively adjoin all sequence carriers, always preserving the same base. -/
noncomputable def tower (Xs : ℕ → Type u) [∀ n, MetricSpace (Xs n)]
    [∀ n, CompactSpace (Xs n)] [∀ n, Nonempty (Xs n)] : ℕ → BasedAmbient X
  | 0 => ⟨X, inferInstance, id, isometry_id⟩
  | n + 1 => (tower Xs n).attach (Xs n)

noncomputable def towerStep (Xs : ℕ → Type u) [∀ n, MetricSpace (Xs n)]
    [∀ n, CompactSpace (Xs n)] [∀ n, Nonempty (Xs n)] (n : ℕ) :
    (tower (X := X) Xs n).Carrier → (tower (X := X) Xs (n + 1)).Carrier :=
  (tower Xs n).inclusion (Xs n)

theorem towerStep_isometry (Xs : ℕ → Type u) [∀ n, MetricSpace (Xs n)]
    [∀ n, CompactSpace (Xs n)] [∀ n, Nonempty (Xs n)] (n : ℕ) :
    Isometry (towerStep (X := X) Xs n) := (tower Xs n).inclusion_isometry (Xs n)

theorem towerStep_base (Xs : ℕ → Type u) [∀ n, MetricSpace (Xs n)]
    [∀ n, CompactSpace (Xs n)] [∀ n, Nonempty (Xs n)] (n : ℕ) :
    towerStep Xs n ∘ (tower (X := X) Xs n).base = (tower Xs (n + 1)).base := rfl
end BasedAmbient
end PaperN.PartI
