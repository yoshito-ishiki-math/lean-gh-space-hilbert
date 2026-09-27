import PaperN.PartI.CommonBaseGluing
import PaperN.PartI.GHPDistance
import PaperN.PartI.ProkhorovIsometry
import PaperN.PartI.ZeroDistanceCouplings

namespace PaperN.PartI
open Metric Set MeasureTheory
universe u
namespace BasedAmbient
variable {X Y : MeasuredCompact.{u}}

/-- Attach a prescribed measured coupling, preserving the fixed base. -/
noncomputable def attachCoupling (A : BasedAmbient X) (C : CompactCoupling X Y) :
    BasedAmbient X where
  Carrier := GlueSpace A.base_isometry C.left_isometry
  metric := inferInstance
  base := toGlueL A.base_isometry C.left_isometry ∘ A.base
  base_isometry := (toGlueL_isometry _ _).comp A.base_isometry

variable {Ys : ℕ → MeasuredCompact.{u}}

noncomputable def couplingTower (C : ∀ n, CompactCoupling X (Ys n)) : ℕ → BasedAmbient X
  | 0 => ⟨X, inferInstance, id, isometry_id⟩
  | n + 1 => (couplingTower C n).attachCoupling (C n)

noncomputable def couplingStep (C : ∀ n, CompactCoupling X (Ys n)) (n : ℕ) :
    (couplingTower C n).Carrier → (couplingTower C (n + 1)).Carrier :=
  toGlueL (couplingTower C n).base_isometry (C n).left_isometry

theorem couplingStep_isometry (C : ∀ n, CompactCoupling X (Ys n)) (n : ℕ) :
    Isometry (couplingStep C n) := toGlueL_isometry _ _

abbrev CouplingJointCarrier (C : ∀ n, CompactCoupling X (Ys n)) :=
  Metric.InductiveLimit (couplingStep_isometry C)

noncomputable def couplingJointBase (C : ∀ n, CompactCoupling X (Ys n)) :
    X → CouplingJointCarrier C :=
  toInductiveLimit (couplingStep_isometry C) 0 ∘ (couplingTower C 0).base

noncomputable def couplingJointMap (C : ∀ n, CompactCoupling X (Ys n)) (n : ℕ) :
    C n → CouplingJointCarrier C :=
  toInductiveLimit (couplingStep_isometry C) (n + 1) ∘
    toGlueR (couplingTower C n).base_isometry (C n).left_isometry

theorem couplingJointBase_at (C : ∀ n, CompactCoupling X (Ys n)) (n : ℕ) :
    toInductiveLimit (couplingStep_isometry C) n ∘ (couplingTower C n).base =
      couplingJointBase C := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change toInductiveLimit (couplingStep_isometry C) (n + 1) ∘
      (couplingStep C n ∘ (couplingTower C n).base) = _
    rw [← Function.comp_assoc, toInductiveLimit_commute, ih]

theorem couplingJointBase_isometry (C : ∀ n, CompactCoupling X (Ys n)) :
    Isometry (couplingJointBase C) :=
  (toInductiveLimit_isometry _ _).comp (couplingTower C 0).base_isometry

theorem couplingJointMap_isometry (C : ∀ n, CompactCoupling X (Ys n)) (n : ℕ) :
    Isometry (couplingJointMap C n) :=
  (toInductiveLimit_isometry _ _).comp (toGlueR_isometry _ _)

/-- Every prescribed coupling has exactly the same copy of the left carrier. -/
theorem couplingJointMap_left (C : ∀ n, CompactCoupling X (Ys n)) (n : ℕ) :
    couplingJointMap C n ∘ (C n).left = couplingJointBase C := by
  rw [← couplingJointBase_at C (n + 1)]
  change (toInductiveLimit (couplingStep_isometry C) (n + 1) ∘
    toGlueR (couplingTower C n).base_isometry (C n).left_isometry) ∘ (C n).left =
    toInductiveLimit (couplingStep_isometry C) (n + 1) ∘
      (toGlueL (couplingTower C n).base_isometry (C n).left_isometry ∘
        (couplingTower C n).base)
  funext x
  exact congrArg (toInductiveLimit (couplingStep_isometry C) (n + 1))
    (congrFun (toGlue_commute (couplingTower C n).base_isometry (C n).left_isometry) x).symm

/-- Hausdorff errors are preserved exactly in the simultaneous realization. -/
theorem couplingJoint_hausdorffEDist (C : ∀ n, CompactCoupling X (Ys n)) (n : ℕ) :
    hausdorffEDist (range (couplingJointBase C))
      (range (couplingJointMap C n ∘ (C n).right)) =
      hausdorffEDist (range (C n).left) (range (C n).right) := by
  rw [← couplingJointMap_left C n, range_comp, range_comp,
    hausdorffEDist_image (couplingJointMap_isometry C n)]

/-- Prokhorov errors are preserved exactly; the joint carrier need not be compact. -/
theorem couplingJoint_levyProkhorovEDist (C : ∀ n, CompactCoupling X (Ys n))
    [MeasurableSpace (CouplingJointCarrier C)] [BorelSpace (CouplingJointCarrier C)]
    (n : ℕ) :
    levyProkhorovEDist (Measure.map (couplingJointBase C) X.measure)
      (Measure.map (couplingJointMap C n ∘ (C n).right) (Ys n).measure) =
      levyProkhorovEDist (C n).leftMeasure (C n).rightMeasure := by
  rw [← couplingJointMap_left C n,
    ← Measure.map_map (couplingJointMap_isometry C n).continuous.measurable
      (C n).left_isometry.continuous.measurable,
    ← Measure.map_map (couplingJointMap_isometry C n).continuous.measurable
      (C n).right_isometry.continuous.measurable]
  exact levyProkhorovEDist_map_isometry _ (couplingJointMap_isometry C n) _ _
end BasedAmbient

/-- Zero GHP distance has simultaneous realizations with both errors tending to zero.
Compactness of a restricted union, and the limiting isometry, are separate steps. -/
theorem zero_ghp_common_ambient (X Y : MeasuredCompact.{u}) (h : ghpDist X Y = 0) :
    ∃ (Z : Type u) (m : MetricSpace Z) (b : MeasurableSpace Z),
      @BorelSpace Z m.toUniformSpace.toTopologicalSpace b ∧
      ∃ (e : X → Z) (es : ℕ → Y → Z), Isometry e ∧ (∀ n, Isometry (es n)) ∧
        Filter.Tendsto (fun n ↦ hausdorffDist (range e) (range (es n)))
          Filter.atTop (nhds 0) ∧
        Filter.Tendsto (fun n ↦ levyProkhorovDist (Measure.map e X.measure)
          (Measure.map (es n) Y.measure)) Filter.atTop (nhds 0) := by
  obtain ⟨C, _, hh, hp⟩ := exists_couplings_tendsto_zero_of_ghpDist_eq_zero X Y h
  let Z := BasedAmbient.CouplingJointCarrier C
  letI : MeasurableSpace Z := borel Z
  letI : BorelSpace Z := ⟨rfl⟩
  refine ⟨Z, inferInstance, inferInstance, inferInstance,
    BasedAmbient.couplingJointBase C,
    fun n ↦ BasedAmbient.couplingJointMap C n ∘ (C n).right,
    BasedAmbient.couplingJointBase_isometry C,
    fun n ↦ (BasedAmbient.couplingJointMap_isometry C n).comp (C n).right_isometry,
    ?_, ?_⟩
  · convert hh using 1
    funext n
    exact congrArg ENNReal.toReal (BasedAmbient.couplingJoint_hausdorffEDist C n)
  · convert hp using 1
    funext n
    exact congrArg ENNReal.toReal (BasedAmbient.couplingJoint_levyProkhorovEDist C n)
end PaperN.PartI
