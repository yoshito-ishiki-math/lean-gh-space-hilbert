# Submission handoff

State: official mechanical preflight passed; no registration request sent.
Repository: https://github.com/yoshito-ishiki-math/lean-gh-space-hilbert
Checked commit: 8b25d3fc5b9f2a61dffa59e1daa8c9c483f70a46.
Use this exact commit for submission; later documentation commits are not new checked snapshots.
Comparator configuration: comparator.json
Compared declaration: PalomarPaperN.main
Title: Conditional Hilbert-space classification of Gromov--Hausdorff space

The package is substantive, not a thin wrapper: PaperN/ includes the proof chain.
Its Challenge imports Mathlib only. Solution imports the substantive main proof,
never Challenge. Valov is now quantified over Type 1 source spaces and Type 0
target spaces, sufficient for the actual invariant measured GH carrier. This
is stronger than the specialized original input and is intentionally disclosed.

Official full preflight passed on 2026-09-27:
https://github.com/yoshito-ishiki-math/lean-gh-space-hilbert/actions/runs/36293358928
Comparator, NanoDa, con-ron, and the Lean default kernel accepted the solution.
The report is `submission-checks/palomar-preflight-2026-09-27-lean4.35.json`.
`submission-checks/package-hashes.json` records local package hashes.
Local builds and the main-theorem axiom check also passed on Lean v4.35.0-rc3.
The five literature assumptions remain explicit; this is a conditional theorem.

Before an authorized actual submission, read the current agent protocol at
https://submit.palomar-registry.org/llms.txt . This preparation has not invoked
any submission or registration endpoint.
