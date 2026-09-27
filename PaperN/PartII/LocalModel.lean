import PaperN.PartII.ZeroCoordinateClass

namespace PaperN.PartII
open PaperN.Shared PaperN.PartI GromovHausdorff Metric Set Filter
open scoped Topology

/-- The nine local-model conditions, on small whole compact carriers.
The seed probabilities are immaterial: equivariance covers every carrier isometry. -/
structure LocalModel (X₀ : MeasuredCompact.{0}) (τ : ℝ) where
  domain : Set GHSpace
  domain_open : IsOpen domain
  center_mem : toGHSpace X₀ ∈ domain
  dimension : ℕ
  dimension_pos : 0 < dimension
  coordinateClass : ∀ X : MeasuredCompact.{0}, toGHSpace X ∈ domain →
    NormedCoordinateClass X (EuclideanSpace ℝ (Fin dimension))
  error : GHSpace → ℝ
  error_nonneg : ∀ q ∈ domain, 0 ≤ error q
  error_continuous : ContinuousOn error domain
  center_error : error (toGHSpace X₀) < τ
  equivariance : ∀ (X Y : MeasuredCompact.{0}) (hX : toGHSpace X ∈ domain)
    (hY : toGHSpace Y ∈ domain) (e : X ≃ᵢ Y)
    (a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin dimension)))
    (b : NormedCoordinatePair Y (EuclideanSpace ℝ (Fin dimension))),
    Quotient.mk _ a = coordinateClass X hX → Quotient.mk _ b = coordinateClass Y hY →
    ∃ U : EuclideanSpace ℝ (Fin dimension) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin dimension),
      (∀ x, b.coordinates (e x) = U (a.coordinates x)) ∧
      (∀ v, b.norm v = a.norm (U.symm v))
  bound : ∀ (X : MeasuredCompact.{0}) (hX : toGHSpace X ∈ domain)
    (a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin dimension))),
    Quotient.mk _ a = coordinateClass X hX →
    ∀ x, a.norm (a.coordinates x) ≤ 2 * diam (univ : Set X)
  representatives_converge : ∀ (Xs : ℕ → MeasuredCompact.{0}) (X : MeasuredCompact.{0})
    (hXs : ∀ k, toGHSpace (Xs k) ∈ domain) (hX : toGHSpace X ∈ domain)
    (C : CommonRealization Xs X), C.HausdorffConverges →
    ∃ a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin dimension)),
      ∃ as : ∀ k, NormedCoordinatePair (Xs k) (EuclideanSpace ℝ (Fin dimension)),
        Quotient.mk _ a = coordinateClass X hX ∧
        (∀ k, Quotient.mk _ (as k) = coordinateClass (Xs k) (hXs k)) ∧
        Tendsto (fun k ↦ unitNormError (as k).norm a.norm) atTop (𝓝 0) ∧
        ∀ R : ∀ k, Correspondence (Xs k) X,
          Tendsto (fun k ↦ ⨆ z : (R k).rel,
            dist (C.seqMap k z.val.1) (C.limitMap z.val.2)) atTop (𝓝 0) →
          Tendsto (fun k ↦ coordinateError (R k) (as k).coordinates a.coordinates) atTop (𝓝 0)
  error_eq : ∀ (X : MeasuredCompact.{0}) (hX : toGHSpace X ∈ domain)
    (a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin dimension))),
    Quotient.mk _ a = coordinateClass X hX →
    error (toGHSpace X) = ⨆ z : X × X, |a.pseudometric z.1 z.2 - dist z.1 z.2|

/-- A6 follows from the explicit orthogonal witness in A2 for arbitrary representatives. -/
theorem LocalModel.pseudometric_invariant {X₀ : MeasuredCompact.{0}} {τ : ℝ}
    (M : LocalModel X₀ τ) (X Y : MeasuredCompact.{0})
    (hX : toGHSpace X ∈ M.domain) (hY : toGHSpace Y ∈ M.domain) (e : X ≃ᵢ Y)
    (a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin M.dimension)))
    (b : NormedCoordinatePair Y (EuclideanSpace ℝ (Fin M.dimension)))
    (ha : Quotient.mk _ a = M.coordinateClass X hX)
    (hb : Quotient.mk _ b = M.coordinateClass Y hY) (x y : X) :
    b.pseudometric (e x) (e y) = a.pseudometric x y := by
  obtain ⟨U, hc, hn⟩ := M.equivariance X Y hX hY e a b ha hb
  change b.norm (b.coordinates (e x) - b.coordinates (e y)) =
    a.norm (a.coordinates x - a.coordinates y)
  rw [hc, hc, ← U.map_sub, hn, U.symm_apply_apply]

/-- The complete local-model data for a singleton center. -/
noncomputable def singletonLocalModel (hg : GHCommonEmbeddingInput.{0})
    (X₀ : MeasuredCompact.{0}) [Subsingleton X₀] (τ : ℝ) (hτ : 0 < τ) :
    LocalModel X₀ τ where
  domain := singletonModelDomain τ
  domain_open := isOpen_singletonModelDomain hg τ
  center_mem := singleton_mem_singletonModelDomain X₀ τ hτ
  dimension := 1
  dimension_pos := by decide
  coordinateClass := fun X _ ↦ zeroCoordinateClass X
  error := ghDiameter
  error_nonneg := fun _ _ ↦ diam_nonneg
  error_continuous := (continuous_ghDiameter hg).continuousOn
  center_error := singleton_mem_singletonModelDomain X₀ τ hτ
  equivariance := fun _ _ _ _ e a b ha hb ↦ zeroCoordinateClass_equivariance e a b ha hb
  bound := fun _ _ a ha ↦ zeroCoordinateClass_bound a ha
  representatives_converge := by
    intro Xs X _ _ _ _
    obtain ⟨a, as, ha, has, hn, hc⟩ := zeroCoordinateClass_representatives_converge Xs X
    exact ⟨a, as, ha, has, hn, fun R _ ↦ hc R⟩
  error_eq := fun X _ a ha ↦ (zeroCoordinateClass_metric_error X a ha).symm

/-- Existence form of the singleton branch of the local-model theorem. -/
theorem exists_localModel_of_subsingleton (hg : GHCommonEmbeddingInput.{0})
    (X₀ : MeasuredCompact.{0}) [Subsingleton X₀] (τ : ℝ) (hτ : 0 < τ) :
    Nonempty (LocalModel X₀ τ) := ⟨singletonLocalModel hg X₀ τ hτ⟩

end PaperN.PartII
