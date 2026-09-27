import PaperN.Shared.Correspondence
import Mathlib.Topology.ContinuousMap.Compact

namespace PaperN.Shared
open Set Metric GromovHausdorff Filter
open scoped Topology NNReal
universe u v

/-- A pseudometric continuous for the original topology, which may be strictly finer. -/
structure ContinuousPseudometric (X : Type u) [TopologicalSpace X] where
  kernel : C(X × X, ℝ)
  self : ∀ x, kernel (x,x) = 0
  comm : ∀ x y, kernel (x,y) = kernel (y,x)
  triangle : ∀ x y z, kernel (x,z) ≤ kernel (x,y) + kernel (y,z)

instance {X : Type u} [TopologicalSpace X] : CoeFun (ContinuousPseudometric X) (fun _ ↦ X → X → ℝ) :=
  ⟨fun d x y ↦ d.kernel (x,y)⟩

namespace ContinuousPseudometric
variable {X : Type u} [TopologicalSpace X]

/-- A type copy carries the pseudometric topology, without replacing the given topology on X. -/
def Carrier (_d : ContinuousPseudometric X) := X
instance (d : ContinuousPseudometric X) [Nonempty X] : Nonempty d.Carrier := ‹Nonempty X›
instance (d : ContinuousPseudometric X) : PseudoMetricSpace d.Carrier where
  dist := d
  dist_self := d.self
  dist_comm := d.comm
  dist_triangle := d.triangle

abbrev Quotient (d : ContinuousPseudometric X) := SeparationQuotient d.Carrier

def proj (d : ContinuousPseudometric X) (x : X) : d.Quotient :=
  SeparationQuotient.mk (show d.Carrier from x)

theorem proj_surjective (d : ContinuousPseudometric X) : Function.Surjective d.proj :=
  @SeparationQuotient.surjective_mk d.Carrier (inferInstance : TopologicalSpace d.Carrier)

theorem dist_proj (d : ContinuousPseudometric X) (x y : X) : dist (d.proj x) (d.proj y) = d x y :=
  SeparationQuotient.dist_mk _ _

theorem proj_eq_iff (d : ContinuousPseudometric X) (x y : X) : d.proj x = d.proj y ↔ d x y = 0 := by
  rw [← dist_eq_zero, d.dist_proj]

theorem continuous_proj (d : ContinuousPseudometric X) : Continuous d.proj := by
  apply Metric.continuous_iff'.mpr
  intro x ε hε
  simp only [d.dist_proj]
  have hc : Continuous (fun y : X ↦ d.kernel (y,x)) :=
    d.kernel.continuous.comp (continuous_id.prodMk continuous_const)
  have h := hc.continuousAt (x := x)
  have he := h.eventually (gt_mem_nhds (show d.kernel (x,x) < ε by simpa [d.self] using hε))
  exact he

instance (d : ContinuousPseudometric X) [CompactSpace X] : CompactSpace d.Quotient := by
  constructor
  rw [← d.proj_surjective.range_eq]
  exact isCompact_range d.continuous_proj

noncomputable def gh (d : ContinuousPseudometric X) [CompactSpace X] [Nonempty X] : GHSpace :=
  toGHSpace d.Quotient

def ofMetric (X : Type u) [PseudoMetricSpace X] : ContinuousPseudometric X :=
  ⟨⟨fun p ↦ dist p.1 p.2, continuous_dist⟩, dist_self, dist_comm, dist_triangle⟩

theorem nonneg (d : ContinuousPseudometric X) (x y : X) : 0 ≤ d x y :=
  @dist_nonneg d.Carrier _ x y

noncomputable def scale (a : ℝ≥0) (d : ContinuousPseudometric X) : ContinuousPseudometric X where
  kernel := (a : ℝ) • d.kernel
  self x := by simp [d.self]
  comm x y := by change (a : ℝ) * d x y = (a : ℝ) * d y x; exact congrArg (fun z ↦ (a : ℝ) * z) (d.comm x y)
  triangle x y z := by
    change (a : ℝ) * d x z ≤ (a : ℝ) * d x y + (a : ℝ) * d y z
    simpa [mul_add] using mul_le_mul_of_nonneg_left (d.triangle x y z) a.coe_nonneg

noncomputable def add (d e : ContinuousPseudometric X) : ContinuousPseudometric X where
  kernel := d.kernel + e.kernel
  self x := by simp [d.self, e.self]
  comm x y := by change d x y + e x y = d y x + e y x; exact congrArg₂ (· + ·) (d.comm x y) (e.comm x y)
  triangle x y z := by
    change d x z + e x z ≤ (d x y + e x y) + (d y z + e y z)
    linarith [d.triangle x y z, e.triangle x y z]

noncomputable def blend (d e : ContinuousPseudometric X) (t : Set.Icc (0 : ℝ) 1) : ContinuousPseudometric X :=
  (d.scale ⟨1-t.val, sub_nonneg.mpr t.property.2⟩).add (e.scale ⟨t.val,t.property.1⟩)
end ContinuousPseudometric
end PaperN.Shared
