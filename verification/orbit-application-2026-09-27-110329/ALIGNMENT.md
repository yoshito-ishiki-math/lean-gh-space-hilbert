# Orbit AR input: bounded source/application revalidation

Date: 2026-09-27T11:03:29+09:00
Agent: Codex (implementation agent; not independent)

## Formal statement

OrbitARInput assumes a compact Hausdorff topological group with a countable
basis, a metrizable equivariant AR, and a quotient map whose fibers are
exactly its orbits. It concludes that the quotient presentation is a
metrizable AR, with Type-0 ambient spaces.

## Informal alignment

Antonyan 1990, Retraction properties of an orbit space, Theorem 8 (printed
pp.317–318, PDF13–14), Corollary 1 (p.320, PDF16). All three pages were
freshly visually inspected from ghref/2.pdf. The theorem requires that at
least one of X and G have a countable basis; Lean uses the sufficient
stronger assumption on G. Taking H=G gives an AR under the trivial quotient
group action. The metric G-space and continuous action assumptions are
included in IsEquivariantAbsoluteRetract, not omitted.

Lean permits any quotient presentation with exactly the orbit fibers.
A surjective quotient map with those fibers is homeomorphic to the orbit
quotient; AR is preserved under homeomorphism. This is a presentation
specialization, not an assertion about arbitrary images of an AR.
The concrete SphereOrbit projection is proved a quotient map and its equal
images are proved equivalent to the existence of a group translate.
No Lie-group hypothesis or finite-dimensionality is imported from the
intermediate lemmas of the source.

Bounded verdict: pass for this input and application. This is not an
independent audit of the source proof or a Lean proof of OrbitARInput.

## Verification

CheckOrbitApplication.lean prints the input, the actual theorem and axiom
reports for countability, quotient topology, orbit fibers, and the AR
application. All reports contain only standard axioms. The actual theorem
retains exactly the hyperspace and orbit literature inputs.

## Trust boundary

hO and hH remain explicit proposition arguments. Source correspondence
and the application checks do not remove them or prove the final theorem
unconditionally. Review was performed by the implementation agent.

## Reproduction

lake env lean CheckOrbitApplication.lean
Source and Lean files are hashed in sources.sha256. Source images were
rendered with pdftoppm from ghref/2.pdf pages13,14,16.
