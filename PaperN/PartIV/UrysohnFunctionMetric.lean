import PaperN.PartIV.UrysohnFunctionModel
import Mathlib.Topology.MetricSpace.Ultra.Basic

namespace PaperN.PartIV

noncomputable instance UrysohnFunction.metricSpace : MetricSpace UrysohnFunction where
  dist f g := (f.distance g : ℝ)
  dist_self f := by simp
  dist_comm f g := congrArg (fun r : NNReal ↦ (r : ℝ)) (f.distance_comm g)
  dist_triangle f g h := by
    exact_mod_cast (f.distance_ultrametric g h).trans
      (max_le (le_add_of_nonneg_right (zero_le : 0 ≤ g.distance h))
        (le_add_of_nonneg_left (zero_le : 0 ≤ f.distance g)))
  eq_of_dist_eq_zero h := (UrysohnFunction.distance_eq_zero_iff _ _).mp
    (NNReal.coe_eq_zero.mp h)

@[simp] theorem UrysohnFunction.dist_eq (f g : UrysohnFunction) :
    dist f g = (f.distance g : ℝ) := rfl

instance UrysohnFunction.isUltrametricDist : IsUltrametricDist UrysohnFunction where
  dist_triangle_max f g h := by
    exact_mod_cast f.distance_ultrametric g h

/-- Closed distance bounds mean agreement strictly above the threshold. -/
theorem UrysohnFunction.distance_le_iff (f g : UrysohnFunction) (r : NNReal) :
    f.distance g ≤ r ↔ ∀ s, r < s → f s = g s := by
  constructor
  · intro h s hs
    by_contra he
    exact (not_le_of_gt hs) ((f.le_distance g s he).trans h)
  · intro h
    apply f.distance_le g r
    intro s hs
    exact le_of_not_gt (fun hr ↦ hs (h s hr))

/-- For positive radii, open distance bounds mean agreement at and above the radius. -/
theorem UrysohnFunction.distance_lt_iff (f g : UrysohnFunction) (r : NNReal) (hr : 0 < r) :
    f.distance g < r ↔ ∀ s, r ≤ s → f s = g s := by
  constructor
  · intro h s hs
    by_contra he
    exact (not_le_of_gt h) (hs.trans (f.le_distance g s he))
  · intro h
    by_cases he : f = g
    · subst g
      simpa using hr
    · exact lt_of_not_ge (fun hn ↦ (f.distance_spec g he).2.1 (h _ hn))

/-- The metric topology has the manuscript's tail-agreement open balls. -/
theorem UrysohnFunction.mem_ball_iff (f g : UrysohnFunction) (r : NNReal) (hr : 0 < r) :
    g ∈ Metric.ball f (r : ℝ) ↔ ∀ s, r ≤ s → f s = g s := by
  rw [Metric.mem_ball, dist_comm, dist_eq, NNReal.coe_lt_coe]
  exact f.distance_lt_iff g r hr

end PaperN.PartIV
