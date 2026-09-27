import PaperN.PartI.IsometryGraphStatements

namespace PaperN.PartI
open TopologicalSpace Set Metric Filter
open scoped Topology
variable {Z : Type*} [MetricSpace Z]

@[simp] theorem mem_isometryGraph (K : NonemptyCompacts Z) (g : K ≃ᵢ K) (p : Z × Z) :
    p ∈ isometryGraph K g ↔ ∃ x : K, ((x : Z), (g x : Z)) = p := by
  change p ∈ (fun x : K ↦ ((x : Z), (g x : Z))) '' (univ : Set K) ↔ _
  simp only [mem_image, mem_univ, true_and]

/-- Hausdorff convergence supplies convergent approximants to each point of the limit. -/
theorem exists_tendsto_mem_compacts {Ks : ℕ → NonemptyCompacts Z} {K : NonemptyCompacts Z}
    (h : Tendsto Ks atTop (𝓝 K)) {x : Z} (hx : x ∈ K) :
    ∃ xs : ℕ → Z, (∀ n, xs n ∈ Ks n) ∧ Tendsto xs atTop (𝓝 x) := by
  choose xs hmem hd using fun n ↦ (Ks n).isCompact.exists_infDist_eq_dist (Ks n).nonempty x
  refine ⟨xs, hmem, ?_⟩
  have ht := (lipschitz_infDist_set x).continuous.continuousAt.tendsto.comp h
  have hz : infDist x (K : Set Z) = 0 := infDist_zero_of_mem hx
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [Function.comp_def, hz, hd, dist_comm] using ht

/-- The distance-preserving relation property of graphs survives a Hausdorff limit. -/
theorem graph_relation_limit {Rs : ℕ → NonemptyCompacts (Z × Z)}
    {R : NonemptyCompacts (Z × Z)} (hR : Tendsto Rs atTop (𝓝 R))
    (hiso : ∀ n, ∀ p ∈ Rs n, ∀ q ∈ Rs n, dist p.1 q.1 = dist p.2 q.2) :
    ∀ p ∈ R, ∀ q ∈ R, dist p.1 q.1 = dist p.2 q.2 := by
  intro p hp q hq
  obtain ⟨ps, hps, hpt⟩ := exists_tendsto_mem_compacts hR hp
  obtain ⟨qs, hqs, hqt⟩ := exists_tendsto_mem_compacts hR hq
  have h1 := hpt.fst_nhds.dist hqt.fst_nhds
  have h2 := hpt.snd_nhds.dist hqt.snd_nhds
  have he : (fun n ↦ dist (ps n).1 (qs n).1) =
      (fun n ↦ dist (ps n).2 (qs n).2) := funext fun n ↦ hiso n _ (hps n) _ (hqs n)
  rw [he] at h1
  exact tendsto_nhds_unique h1 h2

/-- Two surjective projections and zero distortion reconstruct an onto isometry. -/
theorem exists_isometry_of_graph_relation (K : NonemptyCompacts Z)
    (R : NonemptyCompacts (Z × Z))
    (hfst : Prod.fst '' (R : Set (Z × Z)) = K)
    (hsnd : Prod.snd '' (R : Set (Z × Z)) = K)
    (hd : ∀ p ∈ R, ∀ q ∈ R, dist p.1 q.1 = dist p.2 q.2) :
    ∃ g : K ≃ᵢ K, isometryGraph K g = R := by
  have hex : ∀ x : K, ∃ y : K, ((x : Z), (y : Z)) ∈ R := by
    intro x
    obtain ⟨p, hp, he⟩ := show (x : Z) ∈ Prod.fst '' (R : Set (Z × Z)) from hfst ▸ x.property
    have hy : p.2 ∈ K := by
      change p.2 ∈ (K : Set Z)
      rw [← hsnd]
      exact mem_image_of_mem Prod.snd hp
    change p ∈ R at hp
    exact ⟨⟨p.2, hy⟩, by simpa only [← he, Prod.mk.eta] using hp⟩
  choose f hf using hex
  have hi : Isometry f := Isometry.of_dist_eq fun x y ↦ (hd _ (hf x) _ (hf y)).symm
  have hsur : Function.Surjective f := by
    intro y
    obtain ⟨p, hp, he⟩ := show (y : Z) ∈ Prod.snd '' (R : Set (Z × Z)) from hsnd ▸ y.property
    have hx : p.1 ∈ K := by
      change p.1 ∈ (K : Set Z)
      rw [← hfst]
      exact mem_image_of_mem Prod.fst hp
    let x : K := ⟨p.1, hx⟩
    refine ⟨x, Subtype.ext ?_⟩
    have hh := hd _ (hf x) p hp
    have hz : dist (f x : Z) p.2 = 0 := by simpa [x] using hh.symm
    exact (dist_eq_zero.mp hz).trans he
  let g : K ≃ᵢ K := ⟨Equiv.ofBijective f ⟨hi.injective, hsur⟩, hi⟩
  refine ⟨g, NonemptyCompacts.ext ?_⟩
  ext p
  constructor
  · intro hp
    obtain ⟨x, rfl⟩ := (mem_isometryGraph K g p).mp hp
    exact hf x
  · intro hp
    have hx : p.1 ∈ K := by
      change p.1 ∈ (K : Set Z)
      rw [← hfst]
      exact mem_image_of_mem Prod.fst hp
    let x : K := ⟨p.1, hx⟩
    apply (mem_isometryGraph K g p).mpr
    refine ⟨x, Prod.ext rfl ?_⟩
    have hh := hd _ (hf x) p hp
    change (f x : Z) = p.2
    exact dist_eq_zero.mp (by simpa only [x, dist_self] using hh.symm)

@[simp] theorem isometryGraph_map_fst (K : NonemptyCompacts Z) (g : K ≃ᵢ K) :
    (isometryGraph K g).map Prod.fst continuous_fst = K := by
  apply NonemptyCompacts.ext
  change Prod.fst '' (isometryGraph K g : Set (Z × Z)) = (K : Set Z)
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨x, rfl⟩ := (mem_isometryGraph K g p).mp hp
    exact x.property
  · intro hz
    exact ⟨(z, (g ⟨z, hz⟩ : Z)), (mem_isometryGraph K g _).mpr ⟨⟨z, hz⟩, rfl⟩, rfl⟩

@[simp] theorem isometryGraph_map_snd (K : NonemptyCompacts Z) (g : K ≃ᵢ K) :
    (isometryGraph K g).map Prod.snd continuous_snd = K := by
  apply NonemptyCompacts.ext
  change Prod.snd '' (isometryGraph K g : Set (Z × Z)) = (K : Set Z)
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨x, rfl⟩ := (mem_isometryGraph K g p).mp hp
    exact (g x).property
  · intro hz
    let x := g.symm ⟨z, hz⟩
    refine ⟨((x : Z), (g x : Z)), (mem_isometryGraph K g _).mpr ⟨x, rfl⟩, ?_⟩
    exact congrArg Subtype.val (g.apply_symm_apply ⟨z, hz⟩)

/-- The complete first (graph) assertion of the manuscript lemma, with no cited input. -/
theorem isometryGraphSubsequence_spec [CompactSpace Z] :
    IsometryGraphSubsequenceStatement (Z := Z) := by
  intro Ks K hK gs
  obtain ⟨R, φ, hφ, hR⟩ := CompactSpace.tendsto_subseq (fun n ↦ isometryGraph (Ks n) (gs n))
  have hf : R.map Prod.fst continuous_fst = K := by
    apply tendsto_nhds_unique ((continuous_fst.nonemptyCompacts_map).continuousAt.tendsto.comp hR)
    simpa only [Function.comp_def, isometryGraph_map_fst] using hK.comp hφ.tendsto_atTop
  have hs : R.map Prod.snd continuous_snd = K := by
    apply tendsto_nhds_unique ((continuous_snd.nonemptyCompacts_map).continuousAt.tendsto.comp hR)
    simpa only [Function.comp_def, isometryGraph_map_snd] using hK.comp hφ.tendsto_atTop
  have hd : ∀ p ∈ R, ∀ q ∈ R, dist p.1 q.1 = dist p.2 q.2 := by
    apply graph_relation_limit hR
    intro n p hp q hq
    obtain ⟨x, rfl⟩ := (mem_isometryGraph (Ks (φ n)) (gs (φ n)) p).mp hp
    obtain ⟨y, rfl⟩ := (mem_isometryGraph (Ks (φ n)) (gs (φ n)) q).mp hq
    exact ((gs (φ n)).dist_eq x y).symm
  obtain ⟨g, hg⟩ := exists_isometry_of_graph_relation K R
    (congrArg (fun C : NonemptyCompacts Z ↦ (C : Set Z)) hf)
    (congrArg (fun C : NonemptyCompacts Z ↦ (C : Set Z)) hs) hd
  refine ⟨φ, g, hφ, ?_⟩
  rw [hg]
  exact hR

end PaperN.PartI
