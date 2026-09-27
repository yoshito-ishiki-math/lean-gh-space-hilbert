import PaperN.PartII.LocalModel

namespace PaperN.PartII
open PaperN.PartI
open scoped NNReal
namespace LocalModel
variable {X : MeasuredCompact.{0}} {τ : ℝ} (M : LocalModel X τ)

/-- The manuscript's nonnegative error function on the open model neighborhood. -/
noncomputable def errorMap : C(M.domain, ℝ≥0) :=
  ⟨fun q ↦ ⟨M.error q.val, M.error_nonneg q.val q.property⟩,
    M.error_continuous.restrict.subtype_mk _⟩

@[simp] theorem errorMap_coe (q : M.domain) :
    (M.errorMap q : ℝ) = M.error q.val := rfl

/-- The center error bound in the exact neighborhood-domain formulation. -/
theorem errorMap_center_lt :
    (M.errorMap ⟨GromovHausdorff.toGHSpace X, M.center_mem⟩ : ℝ) < τ :=
  M.center_error
end LocalModel
end PaperN.PartII
