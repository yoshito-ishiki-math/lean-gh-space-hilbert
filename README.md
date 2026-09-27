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
