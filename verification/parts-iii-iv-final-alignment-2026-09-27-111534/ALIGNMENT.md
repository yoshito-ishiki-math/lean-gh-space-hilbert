# Parts III and IV main-statement alignment

Date: 2026-09-27T11:15:34+09:00
Agent: Codex / root; implementation agent, non-independent review.

## Formal statement

Part III: PaperN.PartII.ghSpace_absoluteRetract_main.{v}.
Part IV: PaperN.PartIV.discreteApproximation_main,
hilbertCubeDiscreteApproximation_main and ghSpace_homeomorphic_hilbert_main.
Supporting domination: PaperN.PartII.AmbientKernel.exists_AR_domination.
Frozen source and kernel evidence: ../rebuild-2026-09-27-110435/.

## Informal alignment

Verdict: pass for thm:global-domination, thm:absolute-extensor,
thm:part-iii-main, thm:discrete-approximation and thm:part-iv-main, within
the explicit literature-input boundary. This is a statement alignment,
not an independent review of the manuscript's entire exposition.

### Part III

The domination theorem quantifies every continuous positive real error function
on GH. exists_AR_domination gives a concrete SphereOrbit.Space n, separability,
AR status, continuous forward and realization maps, a continuous nonnegative
real error strictly below the prescribed function, and a jointly continuous
homotopy on GH times the closed unit interval. Both endpoints and the precise
bound dist(H(q,s),H(q,t)) <= abs(s-t)*error(q)/2 match the manuscript.
Its extra track-diameter bound strengthens rather than replaces that bound.
The auxiliary AR is initially stated at ambient universe 0; separability,
nonemptiness (the forward map from nonempty GH), and allUniverses provide its
full ambient-category form when required.

IsAbsoluteRetract means retraction from every closed embedding into every
metrizable ambient, with a continuous left inverse. IsAbsoluteNeighborhoodRetract
uses an open neighborhood containing the closed image. The live GH AR theorem
is polymorphic in the ambient universe v. Applying
IsAbsoluteRetract.isAbsoluteNeighborhoodRetract yields the ANR conclusion
of thm:absolute-extensor at the same v. No separability or completeness
restriction is imposed on these ambient spaces. Empty ambient embeddings are
vacuous since GH is nonempty. No boundedness restriction is present.

The active main theorem instantiates the internally proved metric, Polish,
selection, spectral, eigenvalue, category-enlargement and contractible-extensor
steps. Four literature inputs remain: Valov, equivariant hyperspace AR,
orbit AR, Hanner domination. Their individual source/application alignment
records are linked in MAIN-ALIGNMENT.md.

### Part IV

The manuscript allows compact metrizable domain sequences including empty
members. discreteApproximation_main only needs compact topological domains,
so covers the stated scope without an added hypothesis. Every resulting map
is continuous; cover closeness uses one cover member containing both values,
not separate cover members or an unspecified numeric tolerance.
An indexed nonempty open cover is equivalent here to a set-valued open cover:
coverage of nonempty GH supplies a nonempty index subtype. The Hilbert-cube
wrapper explicitly performs this conversion.

IsDiscreteFamily quantifies every ambient point, including points outside
the union, and a neighborhood meeting at most one indexed image. It is not
merely pairwise disjointness or local finiteness. Empty images satisfy this
condition vacuously. The proof combines locally finite, pairwise disjoint
compact (hence closed in GH) image families. Repeated indices are distinguished.

HilbertCube is the product of countably many closed unit intervals. The
wrapper turns component maps into a continuous map on Nat times HilbertCube
using the discrete topology on Nat, and identifies slice images with component
ranges. The approximation theorem has no remaining literature argument.

The final theorem concludes Nonempty (GHSpace ≃ₜ RealHilbertSpace), where
RealHilbertSpace is lp (fun _ : Nat => Real) 2 with its norm topology. This is
existence of a homeomorphism to real square-summable sequences, not an isometry
or a finite-dimensional approximation. GH remains the ordinary isometry-class
space of nonempty compact metric spaces. Completeness, separability and
nonemptiness are checked in CheckRecognitionApplication; the AR premise comes
from Part III and the approximation premise from the proved Hilbert-cube
wrapper. TorunczykRecognitionInput is the fifth and final explicit input.

## Verification

Fixed-source lake build passed, 4051 jobs. CheckMain, CheckMainStatements,
CheckPartII and all five source-application checks passed. Compiler-visible
axiom reports have only propext, Classical.choice and Quot.sound.
No Lean source changed during this alignment pass.

## Trust boundary

The five inputs remain theorem parameters, not globally declared axioms and
not Lean-proved inhabitants. All claims here are conditional on those inputs.
Their literature correspondence has bounded same-agent records. No independent
kernel, independent mathematical reviewer, or owner check is claimed.

## Reproduction

Reproduce the pinned source archive as described in the rebuild README.
Run lake build and the checks listed in its check-results.json.
Manuscript sources used in this review are pinned by manuscript-hashes.json.
