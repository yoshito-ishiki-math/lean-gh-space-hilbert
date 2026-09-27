# Conditional GH-space Hilbert classification — Palomar preparation

This folder contains the substantive Lean development and a submission-facing
Challenge/Solution pair. Prepared for publication at https://github.com/yoshito-ishiki-math/lean-gh-space-hilbert. No Palomar registration has occurred.

The advertised result is conditional on five literature inputs. It is not an
unconditional Lean proof of the classification. Challenge.lean states all five
assumptions using only Mathlib imports. ValovInput is the general Type-1-to-Type-0 Polish-space
right-inverse consequence; Solution specializes it to the invariant measured GH
projection and applies the established main theorem.

The other input notions mean: retracts from closed embeddings in metrizable
spaces; equivariant retractions under continuous compact-group actions; a basis
of continuum-connected neighborhoods; small homotopy domination by separable
ANRs; and open-cover discrete approximation of countably many Hilbert cubes.
All are explicitly defined in Challenge.lean. RealHilbertSpace is real lp at 2.

The development includes the four main parts and their supporting proofs.
COMPLETION.md and verification/ preserve same-agent alignment and kernel evidence
for the original main theorem. Wrapper-specific checks are in submission-checks/.
The Challenge's single sorry is intentional statement specification, and Solution
never imports Challenge. No other intentional proof hole is introduced.

## Paper

Yoshito Ishiki, **The topology of Gromov--Hausdorff space** (2026).
[arXiv:2609.09639](https://arxiv.org/abs/2609.09639),
[version 4](https://arxiv.org/abs/2609.09639v4), revised 24 September 2026.
DOI: [10.48550/arXiv.2609.09639](https://doi.org/10.48550/arXiv.2609.09639).
The included manuscript is the locally aligned source snapshot; it is not asserted
to be byte-identical to the arXiv version. The Lean result records the conditional
main proof chain, with the five literature inputs below.

## Five literature inputs

1. **Valov — probability laws.** Vesko Valov, *Probability measures and Milyutin
   maps between metric spaces*, Journal of Mathematical Analysis and Applications
   **350**(2) (2009), 723–730.
   [DOI](https://doi.org/10.1016/j.jmaa.2008.06.003),
   [arXiv:0801.1721v2](https://arxiv.org/abs/0801.1721v2).
   Theorem 1.1: the continuous-right-inverse consequence, specialized to Polish
   spaces. Input: `PalomarPaperN.ValovInput`.
2. **Antonyan — equivariant hyperspaces.** Sergey Antonyan, *West's problem on
   equivariant hyperspaces and Banach–Mazur compacta*, Transactions of the American
   Mathematical Society **355**(8) (2003), 3379–3404.
   [DOI](https://doi.org/10.1090/S0002-9947-03-03217-3).
   Proposition 3.1, p.3385; read with the *Corrigendum*, **358**(12) (2006),
   5631–5633, [DOI](https://doi.org/10.1090/S0002-9947-06-04200-0).
   Input: `PaperN.PartII.EquivariantHyperspaceARInput`.
3. **Antonyan — orbit retracts.** S. A. Antonyan, *Retraction properties of an
   orbit space*, Mathematics of the USSR-Sbornik **65**(2) (1990), 305–321.
   [DOI](https://doi.org/10.1070/SM1990v065n02ABEH001311).
   Theorem 8 and Corollary 1, with the countable-basis-on-the-group hypothesis.
   Input: `PaperN.PartII.OrbitARInput`.
4. **Hanner — ANR domination.** Olof Hanner, *Some theorems on absolute
   neighborhood retracts*, Arkiv för Matematik **1**(5) (1951), 389–408.
   [DOI](https://doi.org/10.1007/BF02591376).
   Theorem 7.2(b), p.405, in the separable metrizable category.
   Input: `PaperN.PartII.HannerDominationInput`.
5. **Toruńczyk — Hilbert-space recognition.** H. Toruńczyk, *Characterizing
   Hilbert space topology*, Fundamenta Mathematicae **111**(3) (1981), 247–262.
   [DOI](https://doi.org/10.4064/fm-111-3-247-262).
   Condition (i), p.248, read with *A correction of two papers concerning Hilbert
   manifolds*, **125**(1) (1985), 89–93, Section C,
   [DOI](https://doi.org/10.4064/fm-125-1-89-93).
   Input: `PaperN.PartIV.TorunczykRecognitionInput`.

These are five theorem inputs, with two additional correction papers. Their
inhabitants remain assumptions in Lean. Exact application checks and the
same-agent source alignment are linked in [MAIN-ALIGNMENT.md](MAIN-ALIGNMENT.md).

## Official mechanical preflight

The project now pins Lean **v4.35.0-rc3** and Mathlib
`3cb72cfd416d1b5ec4b930d67648ef036a5df24f`.
Both the Challenge/Solution build and the full package build pass locally;
the main theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
See the [migration record](submission-checks/MIGRATION-4.35.md).
Official Comparator/NanoDa checks on this migrated snapshot are pending.

The [earlier run](https://github.com/yoshito-ishiki-math/lean-gh-space-hilbert/actions/runs/36290916485)
on commit `302ef17c74a5975e49f4171bb86f10daef469ba4` stopped at
`toolchain.unsupported` for Lean v4.32.1, before Comparator or NanoDa.
Its [machine report](submission-checks/palomar-preflight-2026-09-27.json)
is retained as historical evidence.

Run **Palomar mechanical preflight** from the Actions tab. It calls the official
full workflow at the pinned pipeline revision, using `palomar-standard-v1` and
`comparator.json`. The default target is the selected workflow commit; an exact
40-character target commit can also be supplied. Inspect the mechanical report
for `status: pass`. Running this workflow does not submit or register with Palomar.

## Local reproduction

Use the repository harness bootstrap to prepare this folder's pinned dependencies,
or reproduce with an ordinary pinned Lake environment on the submission host.
Run `lake build Challenge Solution`, then `lake env lean CheckSubmission.lean`.
For the official comparison run Comparator with comparator.json in an appropriate
Linux verification environment and enable NanoDa. Local compilation is not a
Comparator or independent-kernel result.

## Remaining publication steps

Comparator/NanoDa must pass in the supported verification environment. This
macOS host has no comparator, lean4export, landrun or nanoda_bin installed.
Publication repository: https://github.com/yoshito-ishiki-math/lean-gh-space-hilbert. Use the full Git commit SHA for submission.
Before actual submission, verify the author/maintainer and provenance metadata
for that published snapshot. Preserve the inherited MIT license notice.

## Policy consulted

https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md
https://github.com/leanprover/comparator

State: preparing. Local packaging does not constitute submission, acceptance,
registration or independent mathematical review.
