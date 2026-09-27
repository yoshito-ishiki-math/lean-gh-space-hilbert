import PaperN.PartII.EventualCoefficientConvergence

namespace PaperN.PartII
open MeasureTheory Filter Topology

/-- A finite orthonormal family supplies exactly the basis data used by coefficient convergence. -/
theorem exists_orthonormalBasis_of_orthonormal {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
    (v : ι → E) (hv : Orthonormal ℝ v) :
    ∃ (S : Submodule ℝ E) (b : OrthonormalBasis ι ℝ S), ∀ i, (b i : E) = v i := by
  classical
  let b := Module.Basis.span hv.linearIndependent
  have ho : Orthonormal ℝ (fun i ↦ b i) := by
    rw [orthonormal_iff_ite] at hv ⊢
    intro i j
    simpa [b, Module.Basis.span_apply] using hv i j
  refine ⟨_, b.toOrthonormalBasis ho, ?_⟩
  intro i
  simp [b, Module.Basis.span_apply]

variable {Z X ι : Type*} (Xs : ℕ → Type*)
  [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [∀ n, MetricSpace (Xs n)] [∀ n, CompactSpace (Xs n)]
  [∀ n, MeasurableSpace (Xs n)] [∀ n, BorelSpace (Xs n)] [Fintype ι]

theorem embedded_orthonormal_family_coefficient_tendsto
    (μs : ∀ n, ProbabilityMeasure (Xs n)) (μ : ProbabilityMeasure X)
    [(μ : Measure X).IsOpenPosMeasure]
    (es : ∀ n, Xs n → Z) (hes : ∀ n, Isometry (es n))
    (e : X → Z) (he : Isometry e)
    (hμ : Tendsto (fun n ↦ (μs n).map (es n))
      atTop (𝓝 (μ.map e)))
    (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [StrictConvexSpace ℝ (Lp ℝ p (μ : Measure X))]
    (vs : ℕ → ι → C(Z, ℝ)) (v : ι → C(Z, ℝ))
    (hv : ∀ i, Tendsto (fun n ↦ vs n i) atTop (𝓝 (v i)))
    (hli : LinearIndependent ℝ (fun i ↦ (v i).comp ⟨e, he.continuous⟩))
    (xs : ∀ n, Xs n) (x : X) (hx : Tendsto (fun n ↦ es n (xs n)) atTop (𝓝 (e x)))
    (hp2 : 2 ≤ p)
    (ho : ∀ᶠ n in atTop, Orthonormal ℝ (fun i ↦
      ContinuousMap.toLp 2 (μs n : Measure (Xs n)) ℝ
        ((vs n i).comp ⟨es n, (hes n).continuous⟩))) :
    Tendsto (fun n ↦ coordinateLpMinimizer (μs n : Measure (Xs n)) p
      (fun i ↦ (vs n i).comp ⟨es n, (hes n).continuous⟩)
      (ContinuousMap.toLp p (μs n : Measure (Xs n)) ℝ (distanceProfile (xs n)))) atTop
      (𝓝 (coordinateLpMinimizer (μ : Measure X) p
        (fun i ↦ (v i).comp ⟨e, he.continuous⟩)
        (ContinuousMap.toLp p (μ : Measure X) ℝ (distanceProfile x)))) := by
  apply embedded_eventually_orthonormal_coordinateLpMinimizer_tendsto
    Xs μs μ es hes e he hμ p hp vs v hv hli xs x hx hp2
  filter_upwards [ho] with n hn
  obtain ⟨S, b, hb⟩ := exists_orthonormalBasis_of_orthonormal _ hn
  exact ⟨S, b, fun i ↦ (hb i).symm⟩

end PaperN.PartII
