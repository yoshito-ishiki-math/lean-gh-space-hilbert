import PaperN.PartIV.CoverScale
import Mathlib.Data.Set.Card

namespace PaperN.PartIV
open PaperN.Shared GromovHausdorff Set

/-- A positive-separated labelled family has exactly as many points as labels. -/
theorem separated_range_card {X : Type*} [MetricSpace X] (n : ℕ) (f : Fin n → X)
    (r : ℝ) (hr : 0 < r) (hf : ∀ i j, i ≠ j → r ≤ dist (f i) (f j)) :
    (range f).Pairwise (fun x y ↦ r ≤ dist x y) ∧ (range f).ncard = n := by
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have h := hf i j hne
    rw [hij, dist_self] at h
    linarith
  refine ⟨?_, ?_⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    exact hf i j (fun h ↦ hij (congrArg f h))
  · simpa using ncard_range_of_injective hinj

/-- Too many separated points force a quantitative GH distance from a packing-bounded space. -/
theorem packing_forces_ghDist
    (X Y : Type*) [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    (n N : ℕ) (hn : N < n) (r : ℝ) (hr : 0 < r)
    (f : Fin n → X) (hf : ∀ i j, i ≠ j → r ≤ dist (f i) (f j))
    (hY : ∀ S : Set Y, S.Pairwise (fun x y ↦ r/2 ≤ dist x y) → S.ncard ≤ N) :
    r/4 ≤ ghDist X Y := by
  by_contra h
  have hd : ghDist X Y < r/4 := lt_of_not_ge h
  obtain ⟨R, hR⟩ := exists_correspondence_distortion X Y (r/4) hd
  choose g hg using fun i : Fin n ↦ R.left_total (f i)
  have hgsep : ∀ i j, i ≠ j → r/2 ≤ dist (g i) (g j) := by
    intro i j hij
    have hdist := hR ⟨(f i, g i), hg i⟩ ⟨(f j, g j), hg j⟩
    have hab := (le_abs_self (dist (f i) (f j) - dist (g i) (g j))).trans hdist
    have hs := hf i j hij
    linarith
  obtain ⟨hs, hcard⟩ := separated_range_card n g (r/2) (by linarith) hgsep
  have hb := hY (range g) hs
  rw [hcard] at hb
  omega

/-- The equilateral fiber survives in the canonical representative of its GH class. -/
theorem equilateralProduct_rep_fiber (n : ℕ) [NeZero n] (q : GHSpace)
    (s : Set.Ioi (0 : ℝ)) :
    ∃ f : Fin n → (equilateralProduct n q s).Rep,
      ∀ i j, i ≠ j → dist (f i) (f j) = s.val := by
  have heq : toGHSpace (q.Rep × Equilateral n s) =
      toGHSpace (equilateralProduct n q s).Rep := by
    rw [GHSpace.toGHSpace_rep]
    simpa only [GHSpace.toGHSpace_rep, equilateralProduct] using
      (productGH_toGHSpace q.Rep (Equilateral n s)).symm
  obtain ⟨e⟩ := toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp heq
  let x : q.Rep := Classical.choice inferInstance
  refine ⟨fun i ↦ e (x, (show Equilateral n s from i)), ?_⟩
  intro i j hij
  rw [e.dist_eq]
  exact equilateralProduct_fiber_dist n s x i j hij

/-- A cardinality-level packing witness in the canonical GH representative. -/
theorem equilateralProduct_rep_packing (n : ℕ) [NeZero n] (q : GHSpace)
    (s : Set.Ioi (0 : ℝ)) :
    ∃ S : Set (equilateralProduct n q s).Rep,
      S.Pairwise (fun x y ↦ s.val ≤ dist x y) ∧ S.ncard = n := by
  obtain ⟨f, hf⟩ := equilateralProduct_rep_fiber n q s
  exact ⟨range f, separated_range_card n f s.val s.property (fun i j hij ↦ (hf i j hij).ge)⟩

/-- Product approximations stay a definite distance from spaces with too few separated points. -/
theorem equilateralProduct_separated_from_packing (n : ℕ) [NeZero n]
    (q z : GHSpace) (s : Set.Ioi (0 : ℝ)) (r : ℝ) (hr : 0 < r) (hrs : r ≤ s.val)
    (N : ℕ) (hN : N < n)
    (hz : ∀ S : Set z.Rep, S.Pairwise (fun x y ↦ r/2 ≤ dist x y) → S.ncard ≤ N) :
    r/4 ≤ dist (equilateralProduct n q s) z := by
  obtain ⟨f, hf⟩ := equilateralProduct_rep_fiber n q s
  have h := packing_forces_ghDist (equilateralProduct n q s).Rep z.Rep n N hN r hr
    f (fun i j hij ↦ hrs.trans (hf i j hij).ge) hz
  simpa only [ghDist, GHSpace.toGHSpace_rep] using h

end PaperN.PartIV
