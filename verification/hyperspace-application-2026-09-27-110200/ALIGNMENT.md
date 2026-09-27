# Equivariant hyperspace input: bounded revalidation

Date: 2026-09-27T11:02:00+09:00
Agent: Codex (implementation agent; not independent)

## Formal statement

EquivariantHyperspaceARInput gives the equivariant AR property of nonempty
compact subsets of a nonempty connected metric G-space with an open basis
of continuum-connected sets. G is compact Hausdorff with continuous action;
the hyperspace action is required to be the set-image action.

## Informal alignment

Fresh visual inspection of ghref/3.pdf PDF7, printed p.3385, verifies
Antonyan 2003 Proposition 3.1 and its definition of local continuum
connectedness. Unlike Theorem 1.1 in the introduction, this proposition
allows arbitrary compact groups, not only compact Lie groups. Thus the
countable product of orthogonal groups is not excluded. The connected
branch gives G-AR. Lean's compact connected subsets containing each pair
match subcontinua; its neighborhood quantification gives an open basis.
The source hyperspace is nonempty compact subsets with Hausdorff/Vietoris
topology, the type used by Lean.

The 2006 correction, ghref/4.pdf PDF1 (printed p.5631), was visually read.
All three pages were read through the saved extraction. It repairs the
weak topology of the G-nerve and associated later lemmas; it does not alter
Proposition 3.1. No Lie-group restriction is introduced into that proposition.

Bounded verdict: pass for the input specialization and concrete application
conditions. No independent reconstruction of the cited proof is claimed.

## Verification

CheckHyperspaceApplication.lean checks the concrete theorem and axiom
reports. SphereOrbitAR explicitly installs the compact Hausdorff product
group, its topological-group structure, continuous action on SphereBlockSum,
and the induced set-image action. Connectedness and a continuum-connected
basis come from the normed vector space. Its proof applies only hH.
All checked declarations report standard axioms only.

## Trust boundary

hH itself is still a literature argument. This is same-agent alignment,
not unconditional kernel verification or independent review.

## Reproduction

lake env lean CheckHyperspaceApplication.lean
Source hashes are in sources.sha256. Visual pages were rendered directly
from ghref/3.pdf page7 and ghref/4.pdf page1 with pdftoppm.
