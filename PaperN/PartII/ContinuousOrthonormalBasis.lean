import PaperN.PartII.ContinuousFamilyBasis

namespace PaperN.PartII
open MeasureTheory
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
  (S : Submodule ℝ C(X, ℝ)) [FiniteDimensional ℝ S]

/-- A finite continuous subspace has a basis orthonormal for its L2 inner product. -/
theorem exists_continuous_orthonormal_basis :
    ∃ n : ℕ, ∃ b : Module.Basis (Fin n) ℝ S,
      n = Module.finrank ℝ S ∧
      Orthonormal ℝ (fun i ↦ continuousToL2 μ (b i)) := by
  let T := (continuousSubspaceL2Map μ S).range
  let e := continuousSubspaceL2Equiv μ S
  let c := stdOrthonormalBasis ℝ T
  let b := c.toBasis.map e.symm
  refine ⟨Module.finrank ℝ T, b, e.finrank_eq.symm, ?_⟩
  have ho := c.orthonormal
  rw [orthonormal_iff_ite] at ho ⊢
  intro i j
  have hi : continuousToL2 μ (b i) = (c i : Lp ℝ 2 μ) := by
    change (e (e.symm (c i)) : Lp ℝ 2 μ) = _
    rw [e.apply_symm_apply]
  have hj : continuousToL2 μ (b j) = (c j : Lp ℝ 2 μ) := by
    change (e (e.symm (c j)) : Lp ℝ 2 μ) = _
    rw [e.apply_symm_apply]
  rw [hi, hj]
  exact ho i j

end PaperN.PartII
