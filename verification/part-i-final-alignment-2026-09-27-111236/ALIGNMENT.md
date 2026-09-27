# Part I main theorem alignment

Date: 2026-09-27T11:12:36+09:00
Agent: Codex / root; implementation agent, non-independent review.

## Formal statement

`PaperN.PartI.currentInvariantAssignment_main` proves
`CurrentInvariantAssignmentStatement.{u}` with only the specialized Valov input.
Source and kernel snapshot: `../rebuild-2026-09-27-110435/`.

## Informal alignment

Verdict: pass for `thm:invariant-measures`, conditional on the disclosed Valov
input. This is not a verdict on all explanatory statements in Part I.

The live theorem is in measures-laws-and-averages.tex lines 162–214.
Its simultaneous existential choice precedes M1, M2 and M3; the formal
existential function has the same ordering and depends on the metric instance.

| Informal requirement | Formal match |
|---|---|
| Every nonempty compact metric pair | Type u with MetricSpace, CompactSpace, Nonempty; metric instance is an argument |
| Probability is Radon | Borel ProbabilityMeasure; compact metric spaces are Polish and probability_innerRegular_polish supplies inner regularity |
| M1 full support | support = Set.univ, for each carrier |
| M2 every isometry | X ≃ᵢ Y, pushforward equality; manuscript introduction lines 700–707 explicitly requires surjectivity |
| M3 arbitrary compact ambient | All Z with MetricSpace and CompactSpace, then all prescribed embeddings es and e |
| Hausdorff convergence | Tendsto of hausdorffDist of their ranges to zero |
| Weak convergence | Tendsto in ProbabilityMeasure's weak topology, characterized by bounded continuous test integrals |
| Same simultaneous choice in all clauses | Single μ; implementation universalProbability is shared |

The existential theorem fixes a carrier universe, with no bound on its level.
`universalProbability_natural` and `universalProbability_tendsto` additionally
allow independent carrier/limit/ambient universes and use the same small
selection. `universalProbability_eq_map` proves independence of the chosen
small representative and identifying isometry.

Empty represented spaces are excluded by the manuscript and by Nonempty.
Empty ambient needs no extra assumption: an embedding of the nonempty limit
provides its inhabitant. Singleton carriers and constant sequences are included;
there is no positive-diameter hypothesis. Compact nonempty images justify the
ordinary finite Hausdorff distance. Invariance under all self-isometries follows
by taking X=Y in M2. No fixed realization is chosen in place of M3's universal
quantifier. The Borel and topology conventions were read against introduction
lines 690–710 and preliminaries-probability.tex lines 14–34.

## Verification

The fixed project build passed (4051 jobs). CheckMainStatements and CheckPartII
include the live main theorem. CheckPartIComplete was additionally run in the
same frozen snapshot and exited 0; its cross-universe transport reports have
no axioms beyond propext, Classical.choice and Quot.sound.

## Trust boundary

Valov remains an explicit theorem argument, as authorized by the owner.
Its source and concrete application have their separate bounded alignment in
`../valov-application-2026-09-27-105632/ALIGNMENT.md`.
This is same-agent mathematical statement alignment and Lean kernel checking,
not independent proof review, an owner check or a proof of Valov inside Lean.

## Reproduction

Use the source archive and pinned dependencies in the rebuild record.
Run lake build, lake env lean CheckMainStatements.lean,
lake env lean CheckPartII.lean and lake env lean CheckPartIComplete.lean.
The manuscript files compared here are pinned by manuscript-hashes.json.
