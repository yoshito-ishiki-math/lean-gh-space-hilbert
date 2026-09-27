import PaperN.PartII.CoordinateDefinitions

namespace PaperN.PartII
open PaperN.Shared
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem seminorm_le_of_unit_bound (p : Seminorm ℝ E) (L : ℝ) (_hL : 0 ≤ L)
    (hp : ∀ v : E, ‖v‖ = 1 → p v ≤ L) (v : E) : p v ≤ L * ‖v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ (ne_of_gt hn)]
  have hh := hp _ hu
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)] at hh
  have := mul_le_mul_of_nonneg_left hh (le_of_lt hn)
  simpa only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hn), one_mul, mul_comm] using this

theorem seminorm_difference_le_of_unit_bound (p q : Seminorm ℝ E) (t : ℝ) (_ht : 0 ≤ t)
    (hpq : ∀ v : E, ‖v‖ = 1 → |p v - q v| ≤ t) (v : E) :
    |p v - q v| ≤ t * ‖v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ (ne_of_gt hn)]
  have hh := hpq _ hu
  simp only [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn),
    ← mul_sub, abs_mul] at hh
  have := mul_le_mul_of_nonneg_left hh (le_of_lt hn)
  simpa only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hn), one_mul, mul_comm] using this

theorem coordinate_pair_estimate (p q : Seminorm ℝ E) (M s t L : ℝ)
    (ht : 0 ≤ t) (hL : 0 ≤ L)
    (hpq : ∀ v, |p v - q v| ≤ t * ‖v‖)
    (hq : ∀ v, q v ≤ L * ‖v‖)
    (a b c d : E) (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M)
    (hac : ‖a-c‖ ≤ s) (hbd : ‖b-d‖ ≤ s) :
    |p (a-b) - q (c-d)| ≤ 2*M*t + 2*L*s := by
  have hab : ‖a-b‖ ≤ 2*M := (norm_sub_le a b).trans (by linarith)
  have hdiff : ‖(a-b)-(c-d)‖ ≤ 2*s := by
    have he : (a-b)-(c-d) = (a-c)-(b-d) := by abel
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith)
  calc
    |p (a-b) - q (c-d)| ≤ |p (a-b)-q (a-b)| + |q (a-b)-q (c-d)| :=
      abs_sub_le _ _ _
    _ ≤ t * ‖a-b‖ + L * ‖(a-b)-(c-d)‖ :=
      add_le_add (hpq _) ((abs_sub_map_le_sub q _ _).trans (hq _))
    _ ≤ 2*M*t + 2*L*s := by
      have h₁ := mul_le_mul_of_nonneg_left hab ht
      have h₂ := mul_le_mul_of_nonneg_left hdiff hL
      nlinarith

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem coordinate_correspondence_estimate [CompactSpace X] [CompactSpace Y]
    [Nonempty X] [Nonempty Y] (R : Correspondence X Y)
    (p q : Seminorm ℝ E) (hp : Continuous p) (hq : Continuous q) (f : C(X,E)) (g : C(Y,E))
    (M s t L : ℝ) (ht : 0 ≤ t) (hL : 0 ≤ L)
    (hM : ∀ x, ‖f x‖ ≤ M) (hs : ∀ z : R.rel, ‖f z.val.1-g z.val.2‖ ≤ s)
    (htunit : ∀ v, ‖v‖ = 1 → |p v-q v| ≤ t)
    (hLunit : ∀ v, ‖v‖ = 1 → q v ≤ L) :
    correspondenceError R (coordinatePseudometric p hp f) (coordinatePseudometric q hq g) ≤
      2*M*t + 2*L*s := by
  apply ciSup_le
  intro z
  exact coordinate_pair_estimate p q M s t L ht hL
    (seminorm_difference_le_of_unit_bound p q t ht htunit)
    (seminorm_le_of_unit_bound q L hL hLunit)
    _ _ _ _ (hM _) (hM _) (hs z.1) (hs z.2)
theorem coordinate_correspondence_sup_estimate [CompactSpace X] [CompactSpace Y]
    [Nonempty X] [Nonempty Y] [ProperSpace E] [Nontrivial E]
    (R : Correspondence X Y) (p q : Seminorm ℝ E) (hp : Continuous p) (hq : Continuous q)
    (f : C(X,E)) (g : C(Y,E)) :
    correspondenceError R (coordinatePseudometric p hp f) (coordinatePseudometric q hq g) ≤
      2 * coordinateBound f * unitNormError p q + 2 * unitNormBound q * coordinateError R f g := by
  let S := Metric.sphere (0 : E) 1
  letI sphereCompact : CompactSpace S := (isCompact_iff_compactSpace).mp (isCompact_sphere (0 : E) 1)
  letI sphereNonempty : Nonempty S := (NormedSpace.sphere_nonempty.mpr (by norm_num : (0:ℝ) ≤ 1)).to_subtype
  have hm : BddAbove (Set.range (fun x ↦ ‖f x‖)) := (isCompact_range f.continuous.norm).bddAbove
  have hc : Continuous (fun z : X × Y ↦ ‖f z.1-g z.2‖) :=
    ((f.continuous.comp continuous_fst).sub (g.continuous.comp continuous_snd)).norm
  have he : BddAbove (Set.range (fun z : R.rel ↦ ‖f z.val.1-g z.val.2‖)) := by
    apply (isCompact_range hc).bddAbove.mono
    rintro b ⟨z,rfl⟩
    exact ⟨z.val,rfl⟩
  have ht : BddAbove (Set.range (fun v : S ↦ |p v-q v|)) :=
    (isCompact_range ((hp.comp continuous_subtype_val).sub (hq.comp continuous_subtype_val)).abs).bddAbove
  have hl : BddAbove (Set.range (fun v : S ↦ q v)) :=
    (isCompact_range (hq.comp continuous_subtype_val)).bddAbove
  have ht0 : 0 ≤ unitNormError p q :=
    (abs_nonneg _).trans (le_ciSup ht (Classical.choice sphereNonempty))
  have hl0 : 0 ≤ unitNormBound q :=
    (apply_nonneg q _).trans (le_ciSup hl (Classical.choice sphereNonempty))
  apply coordinate_correspondence_estimate R p q hp hq f g _ _ _ _ ht0 hl0
  · intro x; exact le_ciSup hm x
  · intro z; exact le_ciSup he z
  · intro v hv
    exact le_ciSup ht ⟨v, by simpa [S] using hv⟩
  · intro v hv
    exact le_ciSup hl ⟨v, by simpa [S] using hv⟩

theorem unitNormBound_attained [ProperSpace E] [Nontrivial E]
    (q : Seminorm ℝ E) (hq : Continuous q) :
    ∃ v : E, ‖v‖ = 1 ∧ q v = unitNormBound q := by
  let S := Metric.sphere (0 : E) 1
  have hne : S.Nonempty := NormedSpace.sphere_nonempty.mpr (by norm_num)
  letI sphereNonempty : Nonempty S := hne.to_subtype
  obtain ⟨v, hv, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn hne hq.continuousOn
  refine ⟨v, by simpa [S] using hv, ?_⟩
  have hb : BddAbove (Set.range (fun w : S ↦ q w)) := by
    refine ⟨q v, ?_⟩
    rintro b ⟨w,rfl⟩
    exact hmax w.property
  apply le_antisymm
  · exact le_ciSup hb ⟨v,hv⟩
  · apply ciSup_le
    intro w
    exact hmax w.property

/-- The manuscript estimate; valid even for seminorms, so in particular for its two norms. -/
theorem coordinate_pseudometric_estimate [CompactSpace X] [CompactSpace Y]
    [Nonempty X] [Nonempty Y] (n : ℕ) [NeZero n]
    (R : Correspondence X Y)
    (p q : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (f : C(X,EuclideanSpace ℝ (Fin n))) (g : C(Y,EuclideanSpace ℝ (Fin n))) :
    correspondenceError R
      (coordinatePseudometric p (seminorm_continuous_finiteDimensional p) f)
      (coordinatePseudometric q (seminorm_continuous_finiteDimensional q) g) ≤
      2 * coordinateBound f * unitNormError p q + 2 * unitNormBound q * coordinateError R f g :=
  coordinate_correspondence_sup_estimate R p q
    (seminorm_continuous_finiteDimensional p) (seminorm_continuous_finiteDimensional q) f g
theorem coordinatePseudometricEstimate_spec : CoordinatePseudometricEstimateStatement := by
  intro X Y _ _ _ _ _ _ n _ R p q f g
  exact coordinate_pseudometric_estimate n R p q f g
end PaperN.PartII
