import PaperN.PartIV.BanachHomeomorphism
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Basis

namespace PaperN.PartIV
open Set TopologicalSpace Polynomial

/-- Continuous real functions on the unit interval with the uniform norm. -/
abbrev IntervalFunctionSpace := C(Icc (0 : ℝ) 1, ℝ)

/-- Restricting real polynomials to the interval is injective. -/
theorem interval_polynomial_injective :
    Function.Injective (Polynomial.toContinuousMapOnAlgHom (Icc (0 : ℝ) 1)) := by
  intro p q hpq
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply (Set.Icc_infinite (by norm_num : (0 : ℝ) < 1)).mono
  intro x hx
  have h := congrArg (fun f : IntervalFunctionSpace ↦ f ⟨x,hx⟩) hpq
  change p.eval x = q.eval x at h
  change (p-q).eval x = 0
  simpa only [Polynomial.eval_sub, sub_eq_zero] using h

/-- The polynomial monomials remain linearly independent as continuous functions. -/
theorem interval_monomials_independent :
    LinearIndependent ℝ (fun n : ℕ ↦
      Polynomial.toContinuousMapOnAlgHom (Icc (0 : ℝ) 1) (Polynomial.X ^ n)) := by
  simpa [Polynomial.coe_basisMonomials, Polynomial.monomial_one_right_eq_X_pow, Function.comp_def] using
    (Polynomial.basisMonomials ℝ).linearIndependent.map'
    (Polynomial.toContinuousMapOnAlgHom (Icc (0 : ℝ) 1)).toLinearMap
    (LinearMap.ker_eq_bot.mpr interval_polynomial_injective)

/-- Continuous functions on the interval are infinite dimensional. -/
theorem intervalFunction_not_finiteDimensional : ¬ FiniteDimensional ℝ IntervalFunctionSpace := by
  intro h
  letI := h
  exact Module.Finite.not_linearIndependent_of_infinite _ interval_monomials_independent

/-- Compact-open separability agrees with the uniform norm topology on the compact interval. -/
theorem intervalFunction_separable : SeparableSpace IntervalFunctionSpace := inferInstance

/-- The uniform norm makes the real continuous function space complete. -/
theorem intervalFunction_complete : CompleteSpace IntervalFunctionSpace := inferInstance

/-- The continuous-function example of the Banach-space consequence. -/
theorem ghSpace_homeomorphic_intervalFunctions
    (h : Nonempty (GromovHausdorff.GHSpace ≃ₜ RealHilbertSpace))
    (hK : KadetsHomeomorphismInput) :
    Nonempty (GromovHausdorff.GHSpace ≃ₜ IntervalFunctionSpace) :=
  ghSpace_homeomorphic_banach_of_homeomorph h hK IntervalFunctionSpace
    intervalFunction_not_finiteDimensional

end PaperN.PartIV
