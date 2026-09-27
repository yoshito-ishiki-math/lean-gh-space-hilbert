import PaperN.PartIV.PackingSeparation
import PaperN.Shared.UniformSeparated

namespace PaperN.PartIV
open PaperN.Shared PaperN.PartI GromovHausdorff Set Filter
open scoped Topology

/-- A compact GH family admits one packing bound at every fixed positive scale. -/
theorem compactFamily_packing_bound (hg : GHCommonEmbeddingInput.{0})
    (K : Set GHSpace) (hK : IsCompact K) (r : ℝ) (hr : 0 < r) :
    ∃ N : ℕ, ∀ q ∈ K, ∀ S : Set q.Rep,
      S.Pairwise (fun x y ↦ r ≤ dist x y) → S.ncard ≤ N := by
  classical
  by_contra h
  push Not at h
  choose q hq S hS hcard using h
  obtain ⟨z, _, φ, hφ, ht⟩ := hK.tendsto_subseq hq
  have ht' : Tendsto (fun k ↦ toGHSpace (q (φ k)).Rep) atTop (𝓝 (toGHSpace z.Rep)) := by
    simpa only [GHSpace.toGHSpace_rep, Function.comp_def] using ht
  obtain ⟨N, _, hN⟩ := uniformSeparated_spec hg
    (fun k ↦ (q (φ k)).Rep) z.Rep ht' r hr
  have hb := (hN (N+1) (S (φ (N+1))) (hS (φ (N+1)))).2
  have hl := hcard (φ (N+1))
  have hi : N+1 ≤ φ (N+1) := hφ.id_le (N+1)
  omega

/-- Uniform separation of every sufficiently large equilateral product from a compact family. -/
theorem compactFamily_avoided_by_products (hg : GHCommonEmbeddingInput.{0})
    (K : Set GHSpace) (hK : IsCompact K) (r : ℝ) (hr : 0 < r) :
    ∃ N : ℕ, ∀ n : ℕ, ∀ [NeZero n], N < n →
      ∀ (q : GHSpace) (s : Set.Ioi (0 : ℝ)), r ≤ s.val →
        ∀ z ∈ K, r/4 ≤ dist (equilateralProduct n q s) z := by
  obtain ⟨N, hN⟩ := compactFamily_packing_bound hg K hK (r/2) (by linarith)
  refine ⟨N, ?_⟩
  intro n _ hn q s hrs z hz
  exact equilateralProduct_separated_from_packing n q z s r hr hrs N hn (hN z hz)

/-- One stage of the recursive approximation: all sufficiently large cardinalities
avoid a prescribed compact previous image by a uniform positive distance. -/
theorem compactDomain_product_step (hg : GHCommonEmbeddingInput.{0})
    {D : Type*} [TopologicalSpace D] [CompactSpace D] [Nonempty D]
    (f : D → GHSpace) (hf : Continuous f)
    {I : Type*} [Nonempty I] (U : I → Set GHSpace)
    (ho : ∀ i, IsOpen (U i)) (hc : ∀ q, ∃ i, q ∈ U i)
    (K : Set GHSpace) (hK : IsCompact K) :
    ∃ r : ℝ, 0 < r ∧ ∃ N : ℕ, ∀ n : ℕ, ∀ [NeZero n], N < n →
      Continuous (fun x ↦ coverProduct n U ho hc (f x)) ∧
      (∀ x, ∃ i, f x ∈ U i ∧ coverProduct n U ho hc (f x) ∈ U i) ∧
      (∀ x z, z ∈ K → r/4 ≤ dist (coverProduct n U ho hc (f x)) z) := by
  have hcont : Continuous (fun x ↦ coverScale U (f x)) :=
    (coverScale_lipschitz U).continuous.comp hf
  obtain ⟨a, _, ha⟩ := isCompact_univ.exists_isMinOn univ_nonempty hcont.continuousOn
  let r := coverScale U (f a)
  have hr : 0 < r := (coverScale_pos_le U ho hc (f a)).1
  obtain ⟨N, hN⟩ := compactFamily_avoided_by_products hg K hK r hr
  refine ⟨r, hr, N, ?_⟩
  intro n _ hn
  refine ⟨(coverProduct_lipschitz n U ho hc).continuous.comp hf,
    fun x ↦ coverProduct_close n U ho hc (f x), ?_⟩
  intro x z hz
  exact hN n hn (f x) (positiveCoverScale U ho hc (f x)) (ha (mem_univ x)) z hz

end PaperN.PartIV
