import PaperN.PartII.DualNormComparison
import PaperN.PartII.CoordinateEstimate

namespace PaperN.PartII
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A definite finite-dimensional seminorm controls the Euclidean norm. -/
theorem exists_norm_le_coordinateNorm (p : Seminorm ℝ E) (hp : ∀ v, p v = 0 → v = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖x‖ ≤ C * p x := by
  let e := (CoordinateNormCarrier.continuousLinearEquiv p hp).symm
  refine ⟨max 1 ‖e.toContinuousLinearMap‖, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x
  have h := e.toContinuousLinearMap.le_opNorm (CoordinateNormCarrier.linearEquiv p hp x)
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (apply_nonneg p x))

omit [FiniteDimensional ℝ E] in
/-- Sphere error and coercivity produce the relative bounds needed for dual comparison. -/
theorem coordinateNorm_relative_of_sphere_error (p q : Seminorm ℝ E) (C ε : ℝ)
    (_hC : 0 ≤ C) (hε : 0 ≤ ε) (hc : ∀ x, ‖x‖ ≤ C * p x)
    (he : ∀ x, ‖x‖ = 1 → |q x - p x| ≤ ε) :
    (∀ x, (1 - ε * C) * p x ≤ q x) ∧ (∀ x, q x ≤ (1 + ε * C) * p x) := by
  have hd (x : E) : |q x - p x| ≤ ε * C * p x :=
    (seminorm_difference_le_of_unit_bound q p ε hε he x).trans
      ((mul_le_mul_of_nonneg_left (hc x) hε).trans_eq (by ring))
  constructor <;> intro x <;> have hh := abs_le.mp (hd x) <;> nlinarith

/-- Uniform sphere error tending to zero gives convergence of the normalized embeddings,
including moving vectors. -/
theorem coordinateDualEmbedding_tendsto_of_sphere_error
    (p : Seminorm ℝ E) (ps : ℕ → Seminorm ℝ E)
    (hp : ∀ v, p v = 0 → v = 0) (hs : ∀ k v, ps k v = 0 → v = 0)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 ≤ ε k)
    (he : ∀ k x, ‖x‖ = 1 → |ps k x - p x| ≤ ε k)
    (hlim : Tendsto ε atTop (𝓝 0)) (xs : ℕ → E) (x : E)
    (hx : Tendsto xs atTop (𝓝 x)) :
    Tendsto (fun k ↦ coordinateDualEmbedding (ps k) (hs k) (xs k)) atTop
      (𝓝 (coordinateDualEmbedding p hp x)) := by
  obtain ⟨C, hC, hc⟩ := exists_norm_le_coordinateNorm p hp
  have hd : Tendsto (fun k ↦ ε k * C) atTop (𝓝 0) := by simpa using hlim.mul_const C
  have hsmall : ∀ᶠ k in atTop, ε k * C < 1 := hd.eventually (gt_mem_nhds zero_lt_one)
  have hpcont : Continuous p :=
    (CoordinateNormCarrier.continuousLinearEquiv p hp).continuous.norm
  have hv : Tendsto (fun k ↦ p (xs k - x)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, sub_self, map_zero] using
      hpcont.continuousAt.tendsto.comp (hx.sub (tendsto_const_nhds (x := x)))
  have hb : Tendsto (fun k ↦ (1 + ε k * C) * p (xs k - x) + ε k * C * p x)
      atTop (𝓝 0) := by
    convert ((tendsto_const_nhds.add hd).mul hv).add (hd.mul_const (p x)) using 1; simp
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _) _ hb
  filter_upwards [hsmall] with k hk
  obtain ⟨hl, hu⟩ := coordinateNorm_relative_of_sphere_error p (ps k) C (ε k) hC.le (hε k) hc (he k)
  calc
    _ ≤ ‖coordinateDualEmbedding (ps k) (hs k) (xs k) - coordinateDualEmbedding (ps k) (hs k) x‖ +
        ‖coordinateDualEmbedding (ps k) (hs k) x - coordinateDualEmbedding p hp x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (1 + ε k * C) * p (xs k - x) + ε k * C * p x := by
      rw [coordinateDualEmbedding_norm_sub]
      exact add_le_add (hu _) (coordinateDualEmbedding_sub_norm_le p (ps k) hp (hs k)
        (ε k * C) (mul_nonneg (hε k) hC.le) hk hl hu x)

/-- The manuscript's sphere-uniform convergence formulation for positive dimension. -/
theorem coordinateDualEmbedding_tendsto [Nontrivial E]
    (p : Seminorm ℝ E) (ps : ℕ → Seminorm ℝ E)
    (hp : ∀ v, p v = 0 → v = 0) (hs : ∀ k v, ps k v = 0 → v = 0)
    (hn : Tendsto (fun k ↦ unitNormError (ps k) p) atTop (𝓝 0))
    (xs : ℕ → E) (x : E) (hx : Tendsto xs atTop (𝓝 x)) :
    Tendsto (fun k ↦ coordinateDualEmbedding (ps k) (hs k) (xs k)) atTop
      (𝓝 (coordinateDualEmbedding p hp x)) := by
  let S := Metric.sphere (0 : E) 1
  letI : Nonempty S := (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)).to_subtype
  have hb (k : ℕ) : BddAbove (Set.range (fun u : S ↦ |ps k u - p u|)) :=
    (isCompact_range (((seminorm_continuous_finiteDimensional (ps k)).comp continuous_subtype_val).sub
      ((seminorm_continuous_finiteDimensional p).comp continuous_subtype_val)).abs).bddAbove
  apply coordinateDualEmbedding_tendsto_of_sphere_error p ps hp hs
    (fun k ↦ unitNormError (ps k) p) _ _ hn xs x hx
  · intro k
    exact (abs_nonneg _).trans (le_ciSup (hb k) (Classical.choice inferInstance))
  · intro k u hu
    exact le_ciSup (hb k) ⟨u, mem_sphere_zero_iff_norm.mpr hu⟩

/-- The normalized embeddings converge uniformly on every Euclidean bounded ball. -/
theorem coordinateDualEmbedding_uniformOn_ball_of_sphere_error
    (p : Seminorm ℝ E) (ps : ℕ → Seminorm ℝ E)
    (hp : ∀ v, p v = 0 → v = 0) (hs : ∀ k v, ps k v = 0 → v = 0)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 ≤ ε k)
    (he : ∀ k x, ‖x‖ = 1 → |ps k x - p x| ≤ ε k)
    (hlim : Tendsto ε atTop (𝓝 0)) (R : ℝ) :
    TendstoUniformlyOn (fun k x ↦ coordinateDualEmbedding (ps k) (hs k) x)
      (coordinateDualEmbedding p hp) atTop {x | ‖x‖ ≤ R} := by
  obtain ⟨C, hC, hc⟩ := exists_norm_le_coordinateNorm p hp
  let L := ‖(CoordinateNormCarrier.continuousLinearEquiv p hp).toContinuousLinearMap‖
  have hL : 0 ≤ L := norm_nonneg _
  have hbound (x : E) : p x ≤ L * ‖x‖ :=
    (CoordinateNormCarrier.continuousLinearEquiv p hp).toContinuousLinearMap.le_opNorm x
  have hd : Tendsto (fun k ↦ ε k * C) atTop (𝓝 0) := by simpa using hlim.mul_const C
  have hb : Tendsto (fun k ↦ ε k * C * (L * R)) atTop (𝓝 0) := by simpa using hd.mul_const (L * R)
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  filter_upwards [hd.eventually (gt_mem_nhds zero_lt_one), hb.eventually (gt_mem_nhds hη)] with k hk hηk
  intro x hx
  obtain ⟨hl, hu⟩ := coordinateNorm_relative_of_sphere_error p (ps k) C (ε k) hC.le (hε k) hc (he k)
  have hemb := coordinateDualEmbedding_sub_norm_le p (ps k) hp (hs k)
    (ε k * C) (mul_nonneg (hε k) hC.le) hk hl hu x
  rw [dist_comm, dist_eq_norm]
  exact (hemb.trans (mul_le_mul_of_nonneg_left
    ((hbound x).trans (mul_le_mul_of_nonneg_left hx hL)) (mul_nonneg (hε k) hC.le))).trans_lt hηk

/-- Sphere-uniform convergence implies uniform representation convergence on bounded balls. -/
theorem coordinateDualEmbedding_uniformOn_ball [Nontrivial E]
    (p : Seminorm ℝ E) (ps : ℕ → Seminorm ℝ E)
    (hp : ∀ v, p v = 0 → v = 0) (hs : ∀ k v, ps k v = 0 → v = 0)
    (hn : Tendsto (fun k ↦ unitNormError (ps k) p) atTop (𝓝 0)) (R : ℝ) :
    TendstoUniformlyOn (fun k x ↦ coordinateDualEmbedding (ps k) (hs k) x)
      (coordinateDualEmbedding p hp) atTop {x | ‖x‖ ≤ R} := by
  let S := Metric.sphere (0 : E) 1
  letI : Nonempty S := (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)).to_subtype
  have hb (k : ℕ) : BddAbove (Set.range (fun u : S ↦ |ps k u - p u|)) :=
    (isCompact_range (((seminorm_continuous_finiteDimensional (ps k)).comp continuous_subtype_val).sub
      ((seminorm_continuous_finiteDimensional p).comp continuous_subtype_val)).abs).bddAbove
  apply coordinateDualEmbedding_uniformOn_ball_of_sphere_error p ps hp hs
    (fun k ↦ unitNormError (ps k) p) _ _ hn R
  · intro k
    exact (abs_nonneg _).trans (le_ciSup (hb k) (Classical.choice inferInstance))
  · intro k u hu
    exact le_ciSup (hb k) ⟨u, mem_sphere_zero_iff_norm.mpr hu⟩

end PaperN.PartII
