# Fixed-source project rebuild

Date: 2026-09-27T11:11:00+09:00
Agent: Codex / root (implementation agent; not independent)

## Formal statement

The nine check modules listed in `check-results.json` are the advertised check
surface. `CheckMainStatements.log` records main theorem signatures and universes.
The final homeomorphism theorem retains five explicit literature arguments.

## Informal alignment

This record establishes the compilation and axiom gate only. The bounded source
alignment records are linked from `../../MAIN-ALIGNMENT.md`; final whole-statement
alignment remains pending. No global evidence upgrade is made here.

## Verification

`lake build` exited 0: 4051 jobs. All nine `lake env lean Check*.lean`
commands exited 0. `source-recheck.json` confirms all 463 recorded source files
match both the frozen copy and working project after checks. `axiom-summary.json`
contains counts and unexpected-axiom results. Harness tests: 29 passed.
Research lint still reports errors; its complete output is preserved separately.

## Trust boundary

Lean's own compiler/kernel, not an independent kernel implementation.
The reported axiom sets contain only propext, Classical.choice and Quot.sound.
Explicit literature arguments are not discharged by this axiom report.
Project artifacts were rebuilt without preexisting project build artifacts.
Dependency artifacts were reused: the temporary snapshot used a package symlink
to the working project's packages. Thus this is not a fully isolated dependency
rebuild. No lake clean was run. `dependencies.json` records pinned revisions and
tracked source state. Future reproductions should use the documented bootstrap
for independent package trees, rather than this temporary symlink arrangement.

## Reproduction

Extract `source.tar.gz` into a fresh directory. Prepare its exact pinned dependency
tree using the repository's `tools/lean_bootstrap.py --project <directory>`.
Run `lake build` there, then `lake env lean <name>.lean` for each name in
`check-results.json`. Compare the source hashes and inspect every axiom report.
The dependency cache is an acceleration layer, not an independent trust check.
