import PaperN.PartII.BlockActionTail

namespace PaperN.PartII
open Filter
open scoped Topology
variable {I : Type*} [DecidableEq I] {B : I → Type*}
    [∀ i, NormedAddCommGroup (B i)] [∀ i, NormedSpace ℝ (B i)]
variable {T : Type*} [TopologicalSpace T]

/-- Continuous actions in each block induce a continuous orbit map on the l1 sum. -/
theorem continuous_blockSumAction_orbit (U : T → ∀ i, B i ≃ₗᵢ[ℝ] B i)
    (hU : ∀ i x, Continuous (fun t ↦ U t i x)) (f : lp B 1) :
    Continuous (fun t ↦ blockSumAction (U t) f) := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have ht := (lp.hasSum_single (by simp : (1 : ENNReal) ≠ ⊤) f)
  have htail : ∀ᶠ s : Finset I in atTop,
      ‖f - ∑ i ∈ s, lp.single 1 i (f i)‖ < ε / 4 := by
    have h := ((tendsto_const_nhds (x := f)).sub ht).norm
    have h0 : Tendsto (fun s : Finset I ↦ ‖f - ∑ i ∈ s, lp.single 1 i (f i)‖)
        atTop (𝓝 0) := by simpa using h
    exact h0.eventually (gt_mem_nhds (by positivity))
  obtain ⟨s, hs⟩ := htail.exists
  have hhead : Continuous (fun z ↦ ∑ i ∈ s, ‖U z i (f i) - U t i (f i)‖) :=
    continuous_finsetSum s (fun i _ ↦ ((hU i (f i)).sub continuous_const).norm)
  have he : ∀ᶠ z in 𝓝 t, (∑ i ∈ s, ‖U z i (f i) - U t i (f i)‖) < ε / 2 := by
    have h0 : Tendsto (fun z ↦ ∑ i ∈ s, ‖U z i (f i) - U t i (f i)‖) (𝓝 t) (𝓝 0) := by
      simpa using hhead.continuousAt.tendsto (x := t)
    exact h0.eventually (gt_mem_nhds (by positivity))
  filter_upwards [he] with z hz
  rw [dist_eq_norm]
  exact (blockSumAction_difference_le (U z) (U t) f s).trans_lt (by linarith)

/-- The same blockwise continuity gives joint continuity in the parameter and vector. -/
theorem continuous_blockSumAction (U : T → ∀ i, B i ≃ₗᵢ[ℝ] B i)
    (hU : ∀ i x, Continuous (fun t ↦ U t i x)) :
    Continuous (fun z : T × lp B 1 ↦ blockSumAction (U z.1) z.2) := by
  rw [continuous_iff_continuousAt]
  intro z
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hf : ∀ᶠ w : T × lp B 1 in 𝓝 z, dist w.2 z.2 < ε / 2 :=
    continuous_snd.continuousAt.tendsto.eventually (Metric.ball_mem_nhds _ (by positivity))
  have hu : ∀ᶠ w : T × lp B 1 in 𝓝 z,
      dist (blockSumAction (U w.1) z.2) (blockSumAction (U z.1) z.2) < ε / 2 :=
    ((continuous_blockSumAction_orbit U hU z.2).comp continuous_fst).continuousAt.tendsto.eventually
      (Metric.ball_mem_nhds _ (by positivity))
  filter_upwards [hf, hu] with w hw hv
  have h := dist_triangle (blockSumAction (U w.1) w.2)
    (blockSumAction (U w.1) z.2) (blockSumAction (U z.1) z.2)
  rw [(blockSumAction (U w.1)).isometry.dist_eq] at h
  linarith

/-- Joint continuity of the sphere-block action under coordinatewise operator continuity. -/
theorem continuous_sphereBlockSumAction (n : ℕ → ℕ)
    (U : T → ∀ i, EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n i)))
    (hU : ∀ i, Continuous (fun t ↦ (U t i).toContinuousLinearEquiv.toContinuousLinearMap)) :
    Continuous (fun z : T × SphereBlockSum n ↦ sphereBlockSumAction n (U z.1) z.2) := by
  apply continuous_blockSumAction (fun t i ↦ orthogonalSphereActionEquiv (U t i))
  intro i f
  exact (continuous_orthogonalSphereAction (fun t ↦ U t i) (hU i)).comp
    (continuous_id.prodMk continuous_const)

/-- The product of the usual operator topologies makes the full action jointly continuous. -/
theorem continuous_sphereBlockSumAction_product (n : ℕ → ℕ) :
    letI : ∀ i, TopologicalSpace (EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n i))) := fun _ ↦ orthogonalOperatorTopology
    Continuous (fun z : (∀ i, EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n i))) × SphereBlockSum n ↦ sphereBlockSumAction n z.1 z.2) := by
  letI : ∀ i, TopologicalSpace (EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n i))) := fun _ ↦ orthogonalOperatorTopology
  apply continuous_sphereBlockSumAction n id
  intro i
  have h : Continuous (fun V : EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n i)) ↦ V.toContinuousLinearEquiv.toContinuousLinearMap) :=
    continuous_induced_dom
  exact h.comp (continuous_apply i)

end PaperN.PartII
