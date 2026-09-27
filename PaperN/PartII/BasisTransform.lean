import PaperN.PartII.GramConvergence

namespace PaperN.PartII
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Z ι : Type*} [MetricSpace Z] [Fintype ι]

/-- Column convention: the i-th transformed function is sum_j A[j,i] v[j]. -/
noncomputable def transformContinuousBasis (A : Matrix ι ι ℝ) (v : ι → C(Z, ℝ)) :
    ι → C(Z, ℝ) := fun i ↦ ∑ j, A j i • v j

@[simp] theorem transformContinuousBasis_one [DecidableEq ι] (v : ι → C(Z, ℝ)) :
    transformContinuousBasis (1 : Matrix ι ι ℝ) v = v := by
  classical
  funext i
  simp [transformContinuousBasis, Matrix.one_apply, ite_smul]

theorem transformContinuousBasis_mem (S : Submodule ℝ C(Z, ℝ))
    (A : Matrix ι ι ℝ) (v : ι → C(Z, ℝ)) (hv : ∀ j, v j ∈ S) (i : ι) :
    transformContinuousBasis A v i ∈ S :=
  S.sum_mem fun j _ ↦ S.smul_mem _ (hv j)

theorem transformContinuousBasis_tendsto
    (As : ℕ → Matrix ι ι ℝ) (A : Matrix ι ι ℝ)
    (vs : ℕ → ι → C(Z, ℝ)) (v : ι → C(Z, ℝ))
    (hA : Tendsto As atTop (𝓝 A))
    (hv : ∀ j, Tendsto (fun n ↦ vs n j) atTop (𝓝 (v j))) (i : ι) :
    Tendsto (fun n ↦ transformContinuousBasis (As n) (vs n) i) atTop
      (𝓝 (transformContinuousBasis A v i)) := by
  apply tendsto_finsetSum
  intro j _
  exact ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hA j)) i).smul (hv j)

theorem transformContinuousBasis_tendsto_identity [DecidableEq ι]
    (As : ℕ → Matrix ι ι ℝ) (vs : ℕ → ι → C(Z, ℝ)) (v : ι → C(Z, ℝ))
    (hA : Tendsto As atTop (𝓝 1))
    (hv : ∀ j, Tendsto (fun n ↦ vs n j) atTop (𝓝 (v j))) (i : ι) :
    Tendsto (fun n ↦ transformContinuousBasis (As n) (vs n) i) atTop (𝓝 (v i)) := by
  simpa using transformContinuousBasis_tendsto As 1 vs v hA hv i

theorem continuousGram_transform [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (μ : ProbabilityMeasure Z) (A : Matrix ι ι ℝ) (v : ι → C(Z, ℝ)) :
    continuousGram μ (transformContinuousBasis A v) = A.transpose * continuousGram μ v * A := by
  classical
  have hi (j k : ι) : Integrable (fun z ↦ v j z * v k z) (μ : Measure Z) :=
    (BoundedContinuousFunction.mkOfCompact (v j * v k)).integrable _
  ext i l
  simp only [continuousGram, transformContinuousBasis, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
    Matrix.mul_apply, Matrix.transpose_apply]
  simp_rw [show ∀ j k z, A j i * v j z * (A k l * v k z) =
    (A j i * (v j z * v k z)) * A k l by intros; ring]
  rw [integral_finsetSum _ (fun k _ ↦ integrable_finsetSum _ (fun j _ ↦
    ((hi j k).const_mul (A j i)).mul_const (A k l)))]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_finsetSum _ (fun j _ ↦ ((hi j k).const_mul (A j i)).mul_const (A k l))]
  simp_rw [integral_mul_const, integral_const_mul]

end PaperN.PartII
