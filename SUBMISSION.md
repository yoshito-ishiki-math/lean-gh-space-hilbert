# Submission handoff

State: preparing locally; no request sent to the submission service.
Repository: https://github.com/yoshito-ishiki-math/lean-gh-space-hilbert
Commit: use the full commit SHA returned by git rev-parse HEAD for this snapshot.
Comparator configuration: comparator.json
Compared declaration: PalomarPaperN.main
Title: Conditional Hilbert-space classification of Gromov--Hausdorff space

The package is substantive, not a thin wrapper: PaperN/ includes the proof chain.
Its Challenge imports Mathlib only. Solution imports the substantive main proof,
never Challenge. Valov is now quantified over Type 1 source spaces and Type 0
target spaces, sufficient for the actual invariant measured GH carrier. This
is stronger than the specialized original input and is intentionally disclosed.

Before publication, maintainers should use the exact source-hashes.json generated
by the package validation. Run Comparator and NanoDa in a supported Linux
verification environment; do not describe local Lean compilation as their result.
Then choose a public GitHub repository and immutable commit for the prepared
folder. No branch name should be used as a substitute for that commit.

Before an authorized actual submission, read the current agent protocol at
https://submit.palomar-registry.org/llms.txt . This preparation has not invoked
any submission or registration endpoint.
