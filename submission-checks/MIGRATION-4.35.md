# Lean 4.35 migration

Date: 2026-09-27
Agent: Codex (same agent as migration; not independent mathematical review)

## Snapshot

Baseline public commit: `138e6763432d80edb5f7907ccea45c022c3ac725`.
Old Lean: `leanprover/lean4:v4.32.1`.
Old Mathlib: `520045ab14e26149ee970e2e617ca04b09bde5d6`.
New Lean: `leanprover/lean4:v4.35.0-rc3` (compiler commit
`470d5ce1400764999581fd26d5d72b00d990b0f4`).
New Mathlib: `3cb72cfd416d1b5ec4b930d67648ef036a5df24f`.
The enclosing Git commit pins the complete migrated sources and manifest.

## Changes and alignment

The five explicit literature assumptions and Hilbert-homeomorphism conclusion
are retained. In both Challenge and Solution, ValovInput now passes the continuous
map itself to ProbabilityMeasure.map. Its underlying measure remains Measure.map
of the same function; continuity and Borel hypotheses ensure measurability.
The Type-1 source and Type-0 target universes are unchanged.

The substantive development was migrated to the same pushforward API. Other
repairs cover Set.equivOfEq, Set.domRestrict, updated norm/convex-hull lemmas,
explicit coercion reductions, and local restoration of the older elaborator
transparency behavior with backward.isDefEq.respectTransparency=false.
That option affects elaboration, not the kernel or the permitted axiom set.
No new theorem assumption, custom axiom, native_decide, or proof placeholder was
introduced. Challenge retains its one intentional specification placeholder.

This is a same-agent delta alignment check against the previous snapshot and
MAIN-ALIGNMENT.md, not a new independent audit of the manuscript or all Mathlib.
COMPLETION.md and verification/ preserve historical evidence at the old pins.
They are not represented as checks run with the new toolchain.

## Verification

- `lake build Challenge Solution`: passed (9361 jobs).
- `lake build`: passed (4179 jobs).
- `lake env lean CheckSubmission.lean`: passed; PalomarPaperN.main depends only
  on propext, Classical.choice, Quot.sound.
- Source placeholder scan: no proof placeholders in PaperN or Solution.
- `git diff --check`: passed.

Builds used official Mathlib caches on macOS arm64, with independent package
trees prepared by the repository harness bootstrap. Logs are adjacent to this
file. Compiler warnings for deprecated names and style remain.
Comparator and NanoDa are separate gates; consult the official preflight report.

## Reproduction

Install the pinned Lean toolchain, then run `lake update`, `lake exe cache get`,
`lake build Challenge Solution`, `lake build`, and
`lake env lean CheckSubmission.lean`. The repository harness can instead prepare
the pinned dependency tree with `tools/lean_bootstrap.py --project <path> --fetch`.
Run the pinned Palomar mechanical preflight workflow against a full commit SHA.
No Palomar registration is performed by that workflow.

## Official independent mechanical checks

The official full preflight passed for commit
`8b25d3fc5b9f2a61dffa59e1daa8c9c483f70a46` at 2026-09-27T04:23:03Z.
Run: https://github.com/yoshito-ishiki-math/lean-gh-space-hilbert/actions/runs/36293358928
Report: [palomar-preflight-2026-09-27-lean4.35.json](palomar-preflight-2026-09-27-lean4.35.json).
Comparator accepted PalomarPaperN.main. NanoDa, con-ron, and Lean's default kernel
accepted the exported solution. con-ron reported 61128 declarations accepted
with --verified; the report also discloses its in-process Lean.Syntax modelling.
The complete checker configuration and tool digests are in the machine report.
Errors and warnings are empty. This is an independent mechanical check, not an
independent informal mathematical review and not Palomar registration.
