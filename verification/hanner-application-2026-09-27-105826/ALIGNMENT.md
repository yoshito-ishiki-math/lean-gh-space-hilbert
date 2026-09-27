# Hanner domination: bounded source and application check

Date: 2026-09-27T10:58:26+09:00
Agent: Codex (implementation agent; not independent)

## Formal statement

HannerDominationInput requires a separable metric Type-0 X and, for every
positive constant epsilon, a separable metrizable ANR Y, continuous f:X→Y,
g:Y→X, and a jointly continuous homotopy from id to g∘f with each closed-
interval track of diameter strictly less than epsilon. Its conclusion is
ANR in separable metrizable Type-0 ambient spaces.

## Informal alignment

O. Hanner, Some theorems on absolute neighborhood retracts (1951):
printed p.390 (PDF2) fixes the separable metrizable category and joint
continuity convention; printed p.395 (PDF7) defines epsilon-homotopy by
track diameter on 0≤t≤1; Theorem 7.2(b), pp.404–405 (PDF16–17), uses one
metric and every positive epsilon. Images of PDF2, PDF7 and PDF17 were
visually inspected this turn. The theorem heading on PDF16 was located in
the existing extracted text, not newly visually inspected.

Lean retains the fixed metric and constant-error quantifiers, both endpoint
identities, and strict diameter bound. Reversing the homotopy orientation
from the source's composite-to-identity notation is harmless. The auxiliary
ANR assumption covers all metrizable ambient spaces, hence is stronger than
the source's separable category; the conclusion is kept in the source category.
The subsequent category enlargement is supplied by an internal proof, not
silently included in HannerDominationInput.

Bounded verdict: pass for these source-to-input conditions and the actual
application. This is not a new Lean proof of Hanner's recognition theorem
and not independent certification of the complete main theorem.

## Verification

CheckHannerApplication.lean constructs HasSmallANRDomination GHSpace using
only hv, hH and hO. No Hanner input is needed for this premise. The witness
comes from variable-error AR domination specialized to a positive constant;
continuity, separability, homotopy endpoints and track diameter are included
in the verified type. Standard three axioms only were reported.

## Trust boundary

HannerDominationInput remains a literature proposition argument. The
hyperspace/orbit inputs and Valov input remain upstream. No input was removed.

## Reproduction

lake env lean CheckHannerApplication.lean
Source PDF and checked Lean files are hashed in sources.sha256.
PDF7 visual command: pdftoppm -f 7 -singlefile -scale-to 1300 -png
references/items/papers/hanner-1951-anr-domination/original/paper.pdf /tmp/hanner-page7
