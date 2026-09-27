# Torunczyk recognition: bounded source and application revalidation

Date: 2026-09-27T11:00:15+09:00
Agent: Codex (implementation agent; not independent)

## Formal statement

TorunczykRecognitionInput quantifies over nonempty complete separable metric
Type-0 AR spaces and equates homeomorphism to real lp(N,2) with the open-cover
Hilbert-cube discrete approximation property. It remains a proposition input.

## Informal alignment

Fresh visual reading: 1981 paper, printed pp.248–249 (PDF2), condition (i)
and notation; 1985 correction, printed pp.90–91 (PDF2), Section C.
The source uses the countable discrete integer index and Q=[0,1]^N, continuous
maps N×Q→X, every open cover, and image slices forming a discrete family in X.
The refinement condition on pairs of values is exactly membership of both
values in one cover member. Lean uses naturals as a countably infinite index;
reindexing gives the same condition. Its neighborhood definition of discrete
family applies at all points, not only points in the union.

The target real lp(N,2) is the usual separable Hilbert space. Nonemptiness
is explicit. The cited AR input is restricted to Type-0 ambient spaces;
the actual GH AR premise is available in every ambient universe.
Section C repairs the use of Z sets and the proof of Theorem 3.1; it does
not add a hypothesis to the quoted condition (i). This review does not
independently reconstruct that corrected proof.

Bounded verdict: pass for the quoted statement-to-input and GH application
premises. No Lean proof of the recognition equivalence is claimed.

## Verification

CheckRecognitionApplication.lean verifies GH completeness, separability,
nonemptiness, and the input-free discrete approximation premise. It also
checks the AR premise from hv, hH, hO, hD, without using hT. Compiler-visible
axioms for approximation and the final conditional theorem are standard.

## Trust boundary

Recognition is still assumed via hT; upstream AR literature inputs remain.
The five-input conditional main is not an unconditional kernel theorem.
This source review is by the implementation agent, not independent.

## Reproduction

lake env lean CheckRecognitionApplication.lean
Source PDFs and relevant Lean definitions are pinned in sources.sha256.
