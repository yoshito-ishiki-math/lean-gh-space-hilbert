# Four-part main-theorem formalization

Date: 2026-09-27T11:18:50+09:00
Agent: Codex / root
Status: verified-formally (explicit conditional statements only)
Work state: none

## Formal statement

Owner scope: four parts of paperN and the supporting proof chain, as narrowed by
「主定理と関係あるやつだけで良い」. Established literature theorems may remain
explicit arguments, as authorized by the owner. Independent remarks, additional
corollaries and Questions are not completion requirements.

| Manuscript requirement | Advertised formal result | External inputs |
|---|---|---|
| Part I simultaneous invariant full-support selection, M1–M3 | PaperN.PartI.currentInvariantAssignment_main | Valov |
| Part II local models, A1–A9, all concrete carriers | PaperN.PartII.localModel_concrete_main and LocalModel universal APIs | Valov |
| Part III global domination | PaperN.PartII.AmbientKernel.exists_AR_domination instantiated with internal prerequisites | Valov, hyperspace AR, orbit AR |
| Part III unrestricted AR and ANR | PaperN.PartII.ghSpace_absoluteRetract_main and isAbsoluteNeighborhoodRetract | preceding three plus Hanner |
| Part IV compact-domain discrete approximation | PaperN.PartIV.discreteApproximation_main | none |
| Part IV real Hilbert homeomorphism | PaperN.PartIV.ghSpace_homeomorphic_hilbert_main | preceding four plus Torunczyk |

The final conclusion is Nonempty (GHSpace ≃ₜ lp (fun _ : Nat => Real) 2).
This record certifies the implication from five named inputs, not their
inhabitance inside Lean. The unconditional manuscript claim retains its
separate literature and agent-proof evidence.

## Informal alignment

Reviewer: Codex / root. Independent of proof generation: no. Verdict: pass
for the conditional statements in the table, with the exact owner scope.

- [Part I](verification/part-i-final-alignment-2026-09-27-111236/ALIGNMENT.md)
- [Part II](verification/part-ii-final-alignment-2026-09-27-111409/ALIGNMENT.md)
- [Parts III–IV](verification/parts-iii-iv-final-alignment-2026-09-27-111534/ALIGNMENT.md)

These records compare definitions, hypotheses, quantifier order, universe
transport, arbitrary common embeddings, arbitrary coordinate representatives,
empty-domain and singleton cases, all metrizable ambient spaces, and ambient
discreteness. Each pins its manuscript sources by hash.

All five remaining literature inputs have exact-source/application records:
Valov (105632), Hanner (105826), Torunczyk (110015), hyperspace (110200),
orbit (110329), all on 2026-09-27 under verification/. MAIN-ALIGNMENT.md links
the complete paths. The local ghref corpus was used in source verification.

## Verification

[Fixed-source verification](verification/rebuild-2026-09-27-110435/README.md):
463 source/configuration files, source.tar.gz and source-hashes.json; Lean
leanprover/lean4:v4.32.1; mathlib 520045ab14e26149ee970e2e617ca04b09bde5d6.
All nine pinned dependencies matched their recorded Git revisions and had no
tracked source changes. The snapshot is identified by file hashes rather than
a new Git commit; the working tree is uncommitted.

The project rebuild completed 4051 jobs. Nine check modules exited zero.
CheckMainStatements is the separate declaration/type review surface;
CheckMain, CheckPartII, CheckPartIComplete and the five application modules
record compiler-visible axioms. All reported sets are subsets of propext,
Classical.choice, Quot.sound. The 13 lexical trust-scan hits are comments,
not actual placeholders or extra axioms. Axiom reports, not lexical scanning,
are the decisive proof-dependency evidence.

There was no Comparator run or independent kernel check. Lean's own kernel
recompiled project modules in the frozen snapshot. Dependency artifacts were
cached, with a temporary package symlink; this was not a clean dependency
rebuild. Statement alignment was performed by the implementation agent.
Harness tests passed (29); repository lint has preexisting errors, disclosed
in the rebuild log. Harness validation is not mathematical proof evidence.

## Trust boundary

Five explicit theorem parameters remain, with separately checked literature
correspondence: InvariantValovInput, EquivariantHyperspaceARInput, OrbitARInput,
HannerDominationInput and TorunczykRecognitionInput. They are not introduced
as global axioms. Standard axioms do not certify these assumptions as true.
The intermediate GHP, spectral, common-embedding, probability approximation,
category and extensor constructions are supplied by proved Lean declarations.
No owner check, independent reviewer, external publication or registration is
claimed. No unformalized independent corollary is included by implication.

## Reproduction

Extract verification/rebuild-2026-09-27-110435/source.tar.gz to a fresh directory.
From the repository root run:

    uv run python tools/lean_bootstrap.py --project <extracted-directory>

In that directory run lake build and, for every key in check-results.json,
run lake env lean <key>.lean. Expected: all exit zero and no nonstandard axioms.
Use bootstrap for independent dependency trees, not the temporary symlink.
Compare source and manuscript hashes against the supplied manifests.

## Provenance

Owner-directed manuscript formalization, implemented and aligned by Codex/root.
The live manuscript is identified by the three alignment hash manifests.
No new Git commit, push, publication or Palomar registration was performed.

## Palomar

Status: preparing. See README.md and SUBMISSION.md for this local package.
No submission or registration has occurred.

## Limitations

This is completion under the owner's main-theorem scope and citation policy.
It is not a fully self-contained proof of the five imported literature theorems,
nor an independent audit, nor full formalization of every sentence in paperN.

## Canonical implications

The conditional versions of all four main results now have fixed kernel and
same-agent alignment evidence. The unconditional GHT-38 remains proved/agent;
its status is not silently upgraded by the conditional result.
