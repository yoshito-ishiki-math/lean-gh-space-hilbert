# Part II main theorem alignment

Date: 2026-09-27T11:14:09+09:00
Agent: Codex / root; implementation agent, non-independent review.

## Formal statement

`PaperN.PartII.localModel_concrete_main` supplies a LocalModel at every concrete
nonempty compact metric center and positive real tolerance. Its sole external
argument is the specialized Valov input. The returned model has the universal
coordinate-class API. Frozen sources and compiled declarations are recorded in
`../rebuild-2026-09-27-110435/`.

## Informal alignment

Verdict: pass for `thm:local-models` and its coordinate-class definition,
conditional on Valov. Compared spectral-local-models.tex lines 1–95 and 185–351
against LocalModel, NormedCoordinateClass, CoordinateDefinitions,
UniversalLocalClass, UniversalLocalConvergence, LocalErrorMap,
LocalModelExistence and PartII/MainTheorem.

| Requirement | Formal realization |
|---|---|
| Open neighborhood containing the center | domain_open; localModel_concrete_main center-membership equality |
| Integer dimension at least one | dimension : Nat and dimension_pos |
| Continuous nonnegative error on the neighborhood | errorMap : C(M.domain, NNReal), with errorMap_coe |
| A1 simultaneous coordinate classes on every concrete carrier | universalClass of the single returned LocalModel |
| A2 every isometry and every pair of representatives | universalClass_equivariance; real linear isometry equivalence U and inverse norm transformation |
| A3 bound for every representative | universalClass_representative_bound, exact factor 2 times diameter |
| A4 prescribed sequence and common compact ambient | universal_representatives_converge with independent carrier/limit/ambient universes |
| A4 representatives independent of correspondences | existential a, as precedes forall R; R is not a parameter of the existential choice |
| A4 norm convergence | unitNormError is real supremum over the Euclidean unit sphere |
| A4 coordinate convergence | coordinateError is real supremum of Euclidean difference norms over R.rel |
| A5 continuous pseudometric | NormedCoordinatePair.pseudometric, with literal norm-of-coordinate-difference kernel |
| A6 every representative and input isometry | universalClass_pseudometric_invariant |
| A7 exact error formula for every representative | universalClass_error_eq, supremum over X times X |
| A8 continuity | errorMap (equivalently error_continuous restricted to domain) |
| A9 strict center tolerance | localModel_concrete_main and center_error |

NormedCoordinatePair contains a continuous coordinate map and a definite real
seminorm, hence an actual norm. In finite dimension it is continuous without
an additional hypothesis. The relation Equivalent is precisely the orthogonal
orbit relation: real Euclidean linear isometry equivalences implement the
orthogonal matrices, and b.norm(U v)=a.norm(v) is equivalent to the inverse
formula in the manuscript. The quotient does not select a preferred frame.

Nonempty compact carriers match the GH convention. No positive diameter is
assumed: the singleton branch has dimension 1 and zero coordinates with a
definite norm; its error is diameter and the center error is zero. Tolerance
zero is excluded in both statements. The unit sphere is nonempty because the
dimension is positive. Continuity on compact carriers and compact unit spheres
bounds the supremum expressions; correspondences need not be closed, since
their expressions are bounded on the surrounding compact products. No
closedness restriction was added to the universal correspondence clause.

The concrete-center wrapper identifies the small center with the original GH
class. Universal classes are pulled back from that model, and independence of
small representatives is proved by universalClass_eq_comap. The sequence
transport preserves both ambient displacement and coordinate suprema. Thus a
Type-0 construction is not being substituted for the arbitrary-carrier claim.

## Verification

The fixed build passed (4051 jobs). CheckMainStatements prints the concrete
main theorem and universal convergence type. CheckPartII covers the main,
universal representative, error and pseudometric declarations; their axiom
reports contain only propext, Classical.choice and Quot.sound.
No source edit was made during this alignment pass.

## Trust boundary

The local-model existence proof is instantiated with internally proved GHP,
common embedding, spectral, eigenvalue-finiteness and Lp convexity results.
Valov remains explicit through the Part I law selection. This same-agent
alignment is not an independent audit or an owner check. It does not certify
unrelated remarks or applications.

## Reproduction

Use the rebuild source archive and its pinned dependencies. Run lake build,
lake env lean CheckMainStatements.lean and lake env lean CheckPartII.lean.
The manuscript version is identified by manuscript-hashes.json.
