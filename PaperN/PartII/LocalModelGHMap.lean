import PaperN.PartII.LocalModelRestriction
import PaperN.Shared.PseudometricComparison
import PaperN.PartII.MetricApproximationError

namespace PaperN.PartII
open PaperN.Shared PaperN.PartI GromovHausdorff Metric Set

/-- Matching pseudometrics under a carrier bijection define the same GH class. -/
theorem pseudometric_gh_eq_of_equiv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    (e : X ≃ Y) (d : ContinuousPseudometric X) (c : ContinuousPseudometric Y)
    (h : ∀ x y, c (e x) (e y) = d x y) : d.gh = c.gh := by
  let R : Correspondence X Y := {
    rel := {z | z.2 = e z.1}
    left_total := fun x ↦ ⟨e x, rfl⟩
    right_total := fun y ↦ ⟨e.symm y, (e.apply_symm_apply y).symm⟩ }
  letI : Nonempty R.rel := ⟨⟨(Classical.choice (inferInstance : Nonempty X),
    e (Classical.choice (inferInstance : Nonempty X))), rfl⟩⟩
  have he : correspondenceError R d c ≤ 0 := by
    apply ciSup_le
    intro z
    have h1 : z.1.val.2 = e z.1.val.1 := z.1.property
    have h2 : z.2.val.2 = e z.2.val.1 := z.2.property
    simp only [h1, h2, h, sub_self, abs_zero, le_refl]
  apply dist_le_zero.mp
  exact (quotient_ghDist_le R d c).trans (div_nonpos_of_nonpos_of_nonneg he (by norm_num))

/-- Taking the separated quotient of the original metric preserves its GH class. -/
theorem ofMetric_gh (X : Type*) [MetricSpace X] [CompactSpace X] [Nonempty X] :
    (ContinuousPseudometric.ofMetric X).gh = toGHSpace X := by
  let d := ContinuousPseudometric.ofMetric X
  have hi : Isometry d.proj := Isometry.of_dist_eq (fun x y ↦ d.dist_proj x y)
  let e : X ≃ᵢ d.Quotient := ⟨Equiv.ofBijective d.proj ⟨hi.injective, d.proj_surjective⟩, hi⟩
  exact (toGHSpace_eq_toGHSpace_iff_isometryEquiv.mpr ⟨e⟩).symm

namespace LocalModel
variable {X₀ : MeasuredCompact.{0}} {τ : ℝ}

/-- The local approximation map into GH, formed from the assigned pseudometric quotient. -/
noncomputable def ghMap (M : LocalModel X₀ τ) (q : M.domain) : GHSpace :=
  (NormedCoordinateClass.pseudometric _ _ (M.coordinateClass (ghRepresentative q.val)
    (by simpa only [ghRepresentative_class] using q.property))).gh

/-- Every concrete carrier and every coordinate representative computes the same map. -/
theorem ghMap_eq (M : LocalModel X₀ τ) (X : MeasuredCompact.{0})
    (hX : toGHSpace X ∈ M.domain)
    (a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin M.dimension)))
    (ha : Quotient.mk _ a = M.coordinateClass X hX) :
    M.ghMap ⟨toGHSpace X, hX⟩ = a.pseudometric.gh := by
  let Y := ghRepresentative (toGHSpace X)
  have hY : toGHSpace Y ∈ M.domain := by simpa only [Y, ghRepresentative_class] using hX
  obtain ⟨b, hb⟩ := Quotient.exists_rep (M.coordinateClass Y hY)
  obtain ⟨e⟩ := toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp (ghRepresentative_class (toGHSpace X))
  have he := congrArg (NormedCoordinateClass.pseudometric Y (EuclideanSpace ℝ (Fin M.dimension))) hb
  simp only [NormedCoordinateClass.pseudometric_mk] at he
  change (NormedCoordinateClass.pseudometric Y _ (M.coordinateClass Y hY)).gh = _
  rw [← he]
  exact pseudometric_gh_eq_of_equiv e.toEquiv b.pseudometric a.pseudometric
    (M.pseudometric_invariant Y X hY hX e b a hb ha)

/-- Quantitative GH approximation with the sharp half-error factor. -/
theorem ghMap_dist_le (M : LocalModel X₀ τ) (q : M.domain) :
    dist (M.ghMap q) q.val ≤ M.error q.val / 2 := by
  let X := ghRepresentative q.val
  have hX : toGHSpace X ∈ M.domain := by simpa only [X, ghRepresentative_class] using q.property
  obtain ⟨a, ha⟩ := Quotient.exists_rep (M.coordinateClass X hX)
  have he := M.error_eq X hX a ha
  have hd := quotient_ghDist_le_norm a.pseudometric (ContinuousPseudometric.ofMetric X)
  change dist a.pseudometric.gh (ContinuousPseudometric.ofMetric X).gh ≤ _ at hd
  rw [ofMetric_gh, ← uniform_metric_error_eq_norm, ← he] at hd
  have hmap := M.ghMap_eq X hX a ha
  rw [← hmap] at hd
  simpa only [X, ghRepresentative_class] using hd

end LocalModel
end PaperN.PartII
