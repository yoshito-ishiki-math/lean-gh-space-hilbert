import PaperN.PartII.StrongCompactConvergence
import Mathlib.Analysis.SpecificLimits.Normed

namespace PaperN.PartII
open Filter
open scoped Topology

/-- A small square suffices for invertibility of one minus the element. -/
theorem isUnit_one_sub_of_square_norm_lt_one
    {A : Type*} [NormedRing A] [CompleteSpace A] (a : A) (h : ‖a * a‖ < 1) :
    IsUnit (1 - a) := by
  have hc : Commute (1 - a) (1 + a) := by
    change (1 - a) * (1 + a) = (1 + a) * (1 - a)
    noncomm_ring
  have hm : (1 - a) * (1 + a) = 1 - a * a := by noncomm_ring
  exact (hc.isUnit_mul_iff.mp (hm ▸ isUnit_one_sub_of_norm_lt_one h)).1

/-- Collective compactness and strong convergence to zero ensure eventual invertibility. -/
theorem collectivelyCompact_eventually_isUnit_one_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Ts : ℕ → E →L[ℂ] E)
    (hs : ∀ x, Tendsto (fun n ↦ Ts n x) atTop (𝓝 0))
    (hk : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Ts n x ∈ K) :
    ∀ᶠ n in atTop, IsUnit (1 - Ts n) := by
  have hh := collectivelyCompact_difference_square_tendsto Ts 0
    (by simpa using hs) (by simpa using hk)
  have hnorm : Tendsto (fun n ↦ ‖Ts n * Ts n‖) atTop (𝓝 0) := by
    change Tendsto (fun n ↦ ‖(Ts n).comp (Ts n)‖) atTop (𝓝 0)
    simpa using hh
  filter_upwards [hnorm.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn
  exact isUnit_one_sub_of_square_norm_lt_one (Ts n) hn

/-- Strong collectively compact perturbations of an invertible operator are eventually invertible. -/
theorem collectivelyCompact_eventually_isUnit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E) (hu : IsUnit U)
    (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
    (hk : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Us n x - U x ∈ K) :
    ∀ᶠ n in atTop, IsUnit (Us n) := by
  obtain ⟨u, rfl⟩ := hu
  let R : E →L[ℂ] E := ↑u⁻¹
  let Ts := fun n ↦ R.comp ((u : E →L[ℂ] E) - Us n)
  have ht : ∀ x, Tendsto (fun n ↦ Ts n x) atTop (𝓝 0) := by
    intro x
    have hh := R.continuous.continuousAt.tendsto.comp ((tendsto_const_nhds (x := (u : E →L[ℂ] E) x)).sub (hs x))
    simpa [Ts, Function.comp_def, map_sub] using hh
  obtain ⟨K, hK, hmem⟩ := hk
  have htk : ∃ L : Set E, IsCompact L ∧ ∀ n x, ‖x‖ ≤ 1 → Ts n x ∈ L := by
    refine ⟨(fun y ↦ R (-y)) '' K, hK.image (R.continuous.comp continuous_neg), ?_⟩
    intro n x hx
    refine ⟨Us n x - (u : E →L[ℂ] E) x, hmem n x hx, ?_⟩
    simp [Ts, neg_sub]
  filter_upwards [collectivelyCompact_eventually_isUnit_one_sub Ts ht htk] with n hn
  have heq : (u : E →L[ℂ] E) * (1 - Ts n) = Us n := by
    change (u : E →L[ℂ] E) * (1 - ↑u⁻¹ * ((u : E →L[ℂ] E) - Us n)) = Us n
    simp only [mul_sub, mul_one, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    abel
  exact heq ▸ u.isUnit.mul hn
end PaperN.PartII
