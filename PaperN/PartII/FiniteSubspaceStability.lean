import PaperN.PartII.StrongCompactConvergence
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace PaperN.PartII
open Set Filter Metric
open scoped Topology

/-- Strong convergence with a common norm bound preserves injectivity on a
finite-dimensional subspace fixed by the limit operator. -/
theorem eventually_injective_on_finite_subspace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Ps : ℕ → E →L[ℂ] E) (P : E →L[ℂ] E)
    (hs : ∀ x, Tendsto (fun n ↦ Ps n x) atTop (𝓝 (P x)))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n, ‖Ps n‖ ≤ C)
    (S : Submodule ℂ E) [FiniteDimensional ℂ S]
    (hfix : ∀ x : S, P x = x) :
    ∀ᶠ n in atTop, Function.Injective (fun x : S ↦ Ps n x) := by
  let K : Set E := S.subtypeL '' sphere (0 : S) 1
  have hK : IsCompact K := (isCompact_sphere (0 : S) 1).image S.subtypeL.continuous
  have hu := strong_eventually_uniform_on_compact Ps P hs C hC hb K hK
    (1 / 2) (by norm_num)
  filter_upwards [hu] with n hn
  have hnorm : ‖(Ps n - P).comp S.subtypeL‖ ≤ 1 / 2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by norm_num)
    intro x hx
    exact (hn x ⟨x, by simpa using hx, rfl⟩).le
  have hzero : ∀ x : S, Ps n x = 0 → x = 0 := by
    intro x hx
    have he := ((Ps n - P).comp S.subtypeL).le_opNorm x
    have hb' := mul_le_mul_of_nonneg_right hnorm (norm_nonneg x)
    have hv : ((Ps n - P).comp S.subtypeL) x = -(x : E) := by
      change Ps n x - P x = -(x : E)
      rw [hx, hfix]; simp
    rw [hv, norm_neg] at he
    have hn' : ‖x‖ = 0 := by
      have hn0 := norm_nonneg x
      change ‖x‖ ≤ _ at he
      nlinarith
    exact norm_eq_zero.mp hn'
  intro x y hxy
  change Ps n (x : E) = Ps n (y : E) at hxy
  have hz : x - y = 0 := hzero (x-y) (by
    change Ps n ((x : E) - (y : E)) = 0
    rw [map_sub, hxy, sub_self])
  exact sub_eq_zero.mp hz
end PaperN.PartII
