import PaperN.PartIV.RecursiveProducts
import Mathlib.Topology.LocallyFinite

namespace PaperN.PartIV
open PaperN.Shared GromovHausdorff Set

variable {I : Type*} [Nonempty I] (U : I → Set GHSpace)
  (ho : ∀ i, IsOpen (U i)) (hc : ∀ q, ∃ i, q ∈ U i)

/-- Near a fixed GH point, the scale used by a product has a uniform positive lower bound. -/
theorem cardApprox_scale_lower (a : ℕ+) (q z : GHSpace)
    (h : dist (cardApprox a U ho hc q) z < coverScale U z / 8) :
    coverScale U z / 2 ≤ coverScale U q := by
  letI : NeZero a.val := ⟨a.ne_zero⟩
  have he := equilateralProduct_error a.val q (positiveCoverScale U ho hc q)
  change dist (cardApprox a U ho hc q) q ≤ coverScale U q / 2 at he
  have hs := (coverScale_lipschitz U).dist_le_mul z q
  rw [Real.dist_eq] at hs
  norm_num at hs
  have hb := (le_abs_self (coverScale U z - coverScale U q)).trans hs
  have ht := dist_triangle z (cardApprox a U ho hc q) q
  rw [dist_comm z (cardApprox a U ho hc q)] at ht
  have hp := (coverScale_pos_le U ho hc z).1
  linarith

/-- Only bounded product cardinalities can meet a sufficiently small ball at any GH point. -/
theorem cardApprox_local_card_bound (z : GHSpace) :
    ∃ N : ℕ, ∀ (a : ℕ+) (q : GHSpace),
      dist (cardApprox a U ho hc q) z < coverScale U z / 8 → a.val ≤ N := by
  have hp := (coverScale_pos_le U ho hc z).1
  obtain ⟨N, _, hN⟩ := compact_uniform_separated_bound.{0,0}
    z.Rep (coverScale U z / 4) (by positivity)
  refine ⟨N, ?_⟩
  intro a q h
  by_contra hn
  have hna : N < a.val := Nat.lt_of_not_ge hn
  letI : NeZero a.val := ⟨a.ne_zero⟩
  have hs := cardApprox_scale_lower U ho hc a q z h
  have hz : ∀ S : Set z.Rep,
      S.Pairwise (fun x y ↦ (coverScale U z / 2) / 2 ≤ dist x y) → S.ncard ≤ N := by
    intro S hS
    apply (hN z.Rep id isometry_id S ?_).2
    simpa only [div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hS
  have hd := equilateralProduct_separated_from_packing a.val q z
    (positiveCoverScale U ho hc q) (coverScale U z / 2) (by positivity) hs N hna hz
  change (coverScale U z / 2) / 4 ≤ dist (cardApprox a U ho hc q) z at hd
  linarith

/-- Growing cardinalities give local finiteness, even for arbitrary maps and domains. -/
theorem cardApprox_locallyFinite {D : ℕ → Type*} (f : ∀ j, D j → GHSpace)
    (a : ℕ → ℕ+) (ha : ∀ j, j + 1 < (a j).val) :
    LocallyFinite (fun j ↦ range (cardApprox (a j) U ho hc ∘ f j)) := by
  intro z
  obtain ⟨N, hN⟩ := cardApprox_local_card_bound U ho hc z
  refine ⟨Metric.ball z (coverScale U z / 8),
    Metric.ball_mem_nhds z (by have := (coverScale_pos_le U ho hc z).1; positivity), ?_⟩
  apply (Set.finite_le_nat N).subset
  rintro j ⟨y, ⟨x, rfl⟩, hy⟩
  have hb := hN (a j) (f j x) hy
  have hj := ha j
  change j ≤ N
  omega

end PaperN.PartIV
