import PaperN.Shared.Scaling
import Mathlib.Topology.Homotopy.Contractible

namespace PaperN.Shared
open Set Metric GromovHausdorff Filter
open scoped NNReal Topology
universe u v

theorem scaledGH_congr (X : Type u) (Y : Type v)
    [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
    [Nonempty X] [Nonempty Y] (h : toGHSpace X = toGHSpace Y) (a : ℝ≥0) :
    scaledGH a X = scaledGH a Y := by
  apply dist_le_zero.mp
  have hd : ghDist X Y = 0 := by change dist (toGHSpace X) (toGHSpace Y) = 0; rw [h,dist_self]
  simpa [hd] using scaledGH_dist_le X Y a a

theorem scaleGH_toGHSpace (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
    (a : ℝ≥0) : scaleGH a (toGHSpace X) = scaledGH a X :=
  scaledGH_congr _ _ (GHSpace.toGHSpace_rep _) a

theorem scaledGH_one (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X] :
    scaledGH 1 X = toGHSpace X := by
  let d := (ContinuousPseudometric.ofMetric X).scale 1
  have hi : Isometry d.proj := Isometry.of_dist_eq fun x y ↦ by
    rw [d.dist_proj]; change (1 : ℝ) * dist x y = dist x y; simp
  let e : X ≃ᵢ d.Quotient := ⟨Equiv.ofBijective d.proj ⟨hi.injective,d.proj_surjective⟩, hi⟩
  exact (toGHSpace_eq_toGHSpace_iff_isometryEquiv.mpr ⟨e⟩).symm

theorem scaledGH_zero (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X] :
    scaledGH 0 X = pointGH := by
  let d := (ContinuousPseudometric.ofMetric X).scale 0
  have hz (p q : d.Quotient) : dist p q = 0 := by
    obtain ⟨x,rfl⟩ := d.proj_surjective p
    obtain ⟨y,rfl⟩ := d.proj_surjective q
    rw [d.dist_proj]; change (0 : ℝ)*dist x y = 0; simp
  let f : d.Quotient → Unit := fun _ ↦ ()
  have hi : Isometry f := Isometry.of_dist_eq fun p q ↦ by simp [f,hz p q]
  have hs : Function.Surjective f := fun y ↦ ⟨Classical.choice inferInstance, Subsingleton.elim _ _⟩
  exact toGHSpace_eq_toGHSpace_iff_isometryEquiv.mpr ⟨⟨Equiv.ofBijective f ⟨hi.injective,hs⟩,hi⟩⟩

theorem scaleGH_one (q : GHSpace) : scaleGH 1 q = q := by
  rw [scaleGH,scaledGH_one,GHSpace.toGHSpace_rep]

theorem scaleGH_zero (q : GHSpace) : scaleGH 0 q = pointGH := scaledGH_zero q.Rep

theorem scaleGH_point (a : ℝ≥0) : scaleGH a pointGH = pointGH := by
  rw [pointGH, scaleGH_toGHSpace]
  apply dist_le_zero.mp
  have h := scaledGH_dist_le Unit Unit a 1
  have hz : diam (univ : Set Unit) = 0 := diam_subsingleton (Set.subsingleton_univ)
  simpa [scaledGH_one, ghDist, hz] using h

theorem scaleGH_dist_le (q r : GHSpace) (a b : ℝ≥0) :
    dist (scaleGH a q) (scaleGH b r) ≤
      (a : ℝ)*dist q r + |(a : ℝ)-b|/2 * diam (univ : Set r.Rep) := by
  have h := scaledGH_dist_le q.Rep r.Rep a b
  simpa only [scaleGH, ghDist, GHSpace.toGHSpace_rep] using h

theorem continuous_scaleGH : Continuous (fun p : GHSpace × ℝ≥0 ↦ scaleGH p.2 p.1) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_iff_dist_tendsto_zero.mpr
  have ha : Tendsto (fun z : GHSpace × ℝ≥0 ↦ (z.2 : ℝ)) (𝓝 p) (𝓝 (p.2 : ℝ)) :=
    (NNReal.continuous_coe.comp continuous_snd).continuousAt
  have hd : Tendsto (fun z : GHSpace × ℝ≥0 ↦ dist z.1 p.1) (𝓝 p) (𝓝 0) := by
    have hc : Continuous (fun z : GHSpace × ℝ≥0 ↦ dist z.1 p.1) := continuous_fst.dist continuous_const
    simpa only [ContinuousAt, dist_self] using hc.continuousAt (x := p)
  have he := ((ha.sub (tendsto_const_nhds (x := (p.2 : ℝ)))).abs.div_const 2).mul_const (diam (univ : Set p.1.Rep))
  have hh := (ha.mul hd).add he
  simp only [mul_zero, sub_self, abs_zero, zero_div, zero_mul, add_zero] at hh
  exact squeeze_zero (fun _ ↦ dist_nonneg) (fun z ↦ scaleGH_dist_le z.1 p.1 z.2 p.2) hh

theorem continuous_contraction : Continuous (fun p : GHSpace × Set.Icc (0 : ℝ) 1 ↦ contraction p.1 p.2) := by
  have hc : Continuous (fun p : GHSpace × Set.Icc (0 : ℝ) 1 ↦
      (⟨1-p.2.val, sub_nonneg.mpr p.2.property.2⟩ : ℝ≥0)) :=
    (continuous_const.sub (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  exact continuous_scaleGH.comp (continuous_fst.prodMk hc)

theorem contraction_zero (q : GHSpace) : contraction q ⟨0,by norm_num⟩ = q := by
  unfold contraction
  convert scaleGH_one q using 1
  congr 1
  apply Subtype.ext
  simp

theorem contraction_one (q : GHSpace) : contraction q ⟨1,by norm_num⟩ = pointGH := by
  change scaleGH ⟨1-1,by norm_num⟩ q = pointGH
  convert scaleGH_zero q using 1
  congr 1
  apply Subtype.ext
  simp

theorem contraction_point (t : Set.Icc (0 : ℝ) 1) : contraction pointGH t = pointGH :=
  scaleGH_point _

theorem ghSpace_contractible : ContractibleSpace GHSpace := by
  apply (contractible_iff_id_nullhomotopic GHSpace).mpr
  refine ⟨pointGH, ⟨?_⟩⟩
  exact {
    toFun := fun p ↦ contraction p.2 p.1
    continuous_toFun := continuous_contraction.comp continuous_swap
    map_zero_left := contraction_zero
    map_one_left := contraction_one }

theorem scaling_spec : ScalingStatement.{u,v} := scaledGH_dist_le

theorem contraction_toGHSpace (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
    (t : Set.Icc (0 : ℝ) 1) : contraction (toGHSpace X) t =
      scaledGH ⟨1-t.val, sub_nonneg.mpr t.property.2⟩ X := scaleGH_toGHSpace X _

theorem contraction_spec : ContractionStatement.{u} :=
  ⟨contraction_toGHSpace, continuous_contraction, contraction_zero, contraction_one,
    contraction_point, ghSpace_contractible⟩
end PaperN.Shared
