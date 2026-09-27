import PaperN.PartIV.CompactFamilyPacking

namespace PaperN.PartIV
open PaperN.PartI GromovHausdorff Set

/-- A positive cardinality packages the nonempty equilateral factor. -/
noncomputable def cardApprox {I : Type*} [Nonempty I] (a : ℕ+)
    (U : I → Set GHSpace) (ho : ∀ i, IsOpen (U i))
    (hc : ∀ q, ∃ i, q ∈ U i) : GHSpace → GHSpace :=
  @coverProduct I _ a.val ⟨a.ne_zero⟩ U ho hc

theorem cardApprox_continuous {I : Type*} [Nonempty I] (a : ℕ+)
    (U : I → Set GHSpace) (ho : ∀ i, IsOpen (U i))
    (hc : ∀ q, ∃ i, q ∈ U i) : Continuous (cardApprox a U ho hc) := by
  letI : NeZero a.val := ⟨a.ne_zero⟩
  exact (coverProduct_lipschitz a.val U ho hc).continuous

variable {D : ℕ → Type*} [∀ j, TopologicalSpace (D j)] [∀ j, CompactSpace (D j)]
    (f : ∀ j, D j → GHSpace) (hf : ∀ j, Continuous (f j))
    {I : Type*} [Nonempty I] (U : I → Set GHSpace)
    (ho : ∀ i, IsOpen (U i)) (hc : ∀ q, ∃ i, q ∈ U i)

include hf in
/-- A finite prefix can always be extended, including when the next domain is empty. -/
theorem exists_next_cardinality (hg : GHCommonEmbeddingInput.{0}) (j : ℕ)
    (a : Fin j → ℕ+) :
    ∃ b : ℕ+, j+1 < b.val ∧ ∀ k : Fin j,
      Disjoint (range (cardApprox b U ho hc ∘ f j))
        (range (cardApprox (a k) U ho hc ∘ f k.val)) := by
  classical
  by_cases hD : Nonempty (D j)
  · letI : Nonempty (D j) := hD
    let K := ⋃ k : Fin j, range (cardApprox (a k) U ho hc ∘ f k.val)
    have hK : IsCompact K := isCompact_iUnion (fun k ↦
      isCompact_range ((cardApprox_continuous (a k) U ho hc).comp (hf k.val)))
    obtain ⟨r, hr, N, hN⟩ := compactDomain_product_step hg (f j) (hf j) U ho hc K hK
    let b : ℕ+ := ⟨N+j+2, by omega⟩
    letI : NeZero b.val := ⟨b.ne_zero⟩
    have hb : N < b.val := by dsimp [b]; omega
    obtain ⟨_, _, hsep⟩ := hN b.val hb
    refine ⟨b, by dsimp [b]; omega, ?_⟩
    intro k
    apply Set.disjoint_left.mpr
    rintro z ⟨x, rfl⟩ hz
    have hmem : (cardApprox b U ho hc ∘ f j) x ∈ K := mem_iUnion.mpr ⟨k, hz⟩
    have hd := hsep x _ hmem
    change r/4 ≤ dist ((cardApprox b U ho hc ∘ f j) x)
      ((cardApprox b U ho hc ∘ f j) x) at hd
    rw [dist_self] at hd
    linarith
  · letI : IsEmpty (D j) := not_nonempty_iff.mp hD
    refine ⟨⟨j+2, by omega⟩, by simp, ?_⟩
    intro k
    apply Set.disjoint_left.mpr
    rintro z ⟨x, _⟩
    exact isEmptyElim x

include hf in
/-- Strong recursion chooses all cardinalities with growing lower bounds and disjoint images. -/
theorem exists_recursive_cardinalities (hg : GHCommonEmbeddingInput.{0}) :
    ∃ a : ℕ → ℕ+, (∀ j, j+1 < (a j).val) ∧
      ∀ j k, k < j → Disjoint (range (cardApprox (a j) U ho hc ∘ f j))
        (range (cardApprox (a k) U ho hc ∘ f k)) := by
  classical
  let step (j : ℕ) (a : ∀ k, k < j → ℕ+) : ℕ+ :=
    (exists_next_cardinality f hf U ho hc hg j (fun k ↦ a k.val k.isLt)).choose
  let a : ℕ → ℕ+ := Nat.strongRec step
  have ha (j : ℕ) : a j = step j (fun k _ ↦ a k) := Nat.strongRec_eq step j
  have hs (j : ℕ) :=
    (exists_next_cardinality f hf U ho hc hg j (fun k : Fin j ↦ a k.val)).choose_spec
  refine ⟨a, ?_, ?_⟩
  · intro j
    rw [ha]
    exact (hs j).1
  · intro j k hkj
    rw [ha j]
    exact (hs j).2 ⟨k, hkj⟩

include hf in
/-- The recursive products form a cover-close continuous sequence with pairwise disjoint images.
Local finiteness is a separate conclusion, not hidden in this statement. -/
theorem exists_disjoint_product_approximations (hg : GHCommonEmbeddingInput.{0}) :
    ∃ a : ℕ → ℕ+, (∀ j, j+1 < (a j).val) ∧
      (∀ j, Continuous (cardApprox (a j) U ho hc ∘ f j)) ∧
      (∀ j x, ∃ i, f j x ∈ U i ∧ cardApprox (a j) U ho hc (f j x) ∈ U i) ∧
      ∀ j k, j ≠ k → Disjoint (range (cardApprox (a j) U ho hc ∘ f j))
        (range (cardApprox (a k) U ho hc ∘ f k)) := by
  obtain ⟨a, ha, hsep⟩ := exists_recursive_cardinalities f hf U ho hc hg
  refine ⟨a, ha, fun j ↦ (cardApprox_continuous (a j) U ho hc).comp (hf j), ?_, ?_⟩
  · intro j x
    letI : NeZero (a j).val := ⟨(a j).ne_zero⟩
    exact coverProduct_close (a j).val U ho hc (f j x)
  · intro j k hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · exact (hsep k j h).symm
    · exact hsep j k h

end PaperN.PartIV
