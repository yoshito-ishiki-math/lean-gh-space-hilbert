# Valov input and actual application: bounded revalidation

Date: 2026-09-27T10:56:32+09:00
Agent: Codex (same agent as implementation; not independent)

## Formal statement

ValovProbabilityInput.rightInverse assumes a continuous map between Polish
Borel spaces, openness and surjectivity, and returns a continuous right
inverse on the weak probability spaces. InvariantValovInput specializes
this to invariantProjectionMap for the internally proved GHP structures.

## Informal alignment

Source: V. Valov, Probability measures and Milyutin maps between metric
spaces, arXiv:0801.1721v2, source lines 141-202, Theorem 1.1 and the ensuing
right-inverse consequence. Original TeX was read directly. Its conventions
use continuous maps between metrizable spaces, complete means completely
metrizable, and measures are Radon probabilities with bounded-continuous
weak topology. The source distinguishes the compact-support subspace;
that restriction is not used in this input. The theorem assumes an open
surjection between complete spaces. Polish specialization is narrower.
The source's right-inverse consequence has the same pushforward orientation.

Lean's probability_innerRegular_polish supplies compact inner regularity.
ProbabilityMeasure.tendsto_iff_forall_integral_tendsto uses bounded continuous
real test functions, matching the source's weak topology. Valov is used to
produce laws on measured classes; full mass and support inclusion in fibers
are separately deduced. Invariance/full support of the ultimate carrier
assignment are not smuggled into the cited right inverse.

Verdict: pass for this bounded input-to-source specialization and application
hypothesis check. This does not certify the entire Part I assignment or the
other four literature inputs. No new PDF visual check was performed.

## Verification

CheckValovApplication.lean successfully constructs the actual Polish and
continuous/open/surjective projection statements with no external inputs.
The cited right inverse itself remains an explicit uninhabited proposition
input. Compiler axiom reports contain only propext, Classical.choice and
Quot.sound. Source TeX and ghref/57.pdf hashes match the existing register.

## Trust boundary

ValovProbabilityInput has not been proved in Lean. Source matching justifies
the literature boundary; it does not remove it or establish unconditional
kernel verification of the final theorem. This review is not independent.

## Reproduction

From the pinned paperN Lean project: lake env lean CheckValovApplication.lean.
Read the versioned source above; verify the hashes in sources.sha256.
