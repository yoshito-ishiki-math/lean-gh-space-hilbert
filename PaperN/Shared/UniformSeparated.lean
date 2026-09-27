import PaperN.Shared.Statements
import PaperN.PartI.UniverseAssignment

namespace PaperN.Shared
open Set Metric GromovHausdorff Filter PaperN.PartI
open scoped Topology
universe u v w

/-- One packing bound works for every isometric subspace of a compact ambient space. -/
theorem compact_uniform_separated_bound (Z : Type w) [MetricSpace Z] [CompactSpace Z]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ (X : Type u) [MetricSpace X] (e : X → Z), Isometry e →
      ∀ S : Set X, S.Pairwise (fun x y ↦ ε ≤ dist x y) → S.Finite ∧ S.ncard ≤ N := by
  classical
  obtain ⟨T, hT, hcover⟩ := Metric.totallyBounded_iff.mp (isCompact_univ : IsCompact (Set.univ : Set Z)).totallyBounded
    (ε / 3) (by positivity)
  letI := hT.to_subtype
  refine ⟨Nat.card T + 1, by omega, ?_⟩
  intro X _ e he S hS
  have hc (x : S) : ∃ c : T, dist (e x) c < ε / 3 := by
    have hx := hcover (mem_univ (e x))
    simp only [mem_iUnion, mem_ball] at hx
    obtain ⟨c, hc, hd⟩ := hx
    exact ⟨⟨c,hc⟩, hd⟩
  let f : S → T := fun x ↦ (hc x).choose
  have hf : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hs : ε ≤ dist (e x) (e y) := by
      rw [he.dist_eq]
      exact hS x.property y.property (fun h ↦ hne (Subtype.ext h))
    have hx := (hc x).choose_spec
    have hy := (hc y).choose_spec
    change dist (e x) (f x) < ε / 3 at hx
    change dist (e y) (f y) < ε / 3 at hy
    rw [← hxy] at hy
    have ht := dist_triangle (e x) (f x) (e y)
    rw [dist_comm (f x : Z) (e y)] at ht
    linarith
  letI := Finite.of_injective f hf
  exact ⟨Set.toFinite S, (Nat.card_le_card_of_injective f hf).trans (Nat.le_succ _)⟩

theorem uniformSeparated_spec (hg : GHCommonEmbeddingInput.{0}) : UniformSeparatedStatement.{u,v} := by
  intro Xs X _ _ _ _ _ _ h ε hε
  have hr (n) : toGHSpace (smallCarrier (Xs n)) = toGHSpace (Xs n) := ghRepresentative_class _
  have hl : toGHSpace (smallCarrier X) = toGHSpace X := ghRepresentative_class _
  have h' : Tendsto (fun n ↦ toGHSpace (smallCarrier (Xs n))) atTop (𝓝 (toGHSpace (smallCarrier X))) := by
    simpa only [hr, hl] using h
  obtain ⟨C, _⟩ := hg (fun n ↦ smallCarrier (Xs n)) (smallCarrier X) h'
  obtain ⟨N, hN, hb⟩ := compact_uniform_separated_bound.{u,0} C ε hε
  refine ⟨N, hN, ?_⟩
  intro n S hS
  exact hb (Xs n) (C.seqMap n ∘ (smallCarrierEquiv (Xs n)).symm)
    ((C.seq_isometry n).comp (smallCarrierEquiv (Xs n)).symm.isometry) S hS
end PaperN.Shared
