# Formalisation of rooted trees and Butcher series in Lean4

This project aims to formalise rooted trees, their Hopf algebras and Butcher series (B-series) as tools to be used in the analysis of numerical schemes.

## Objects of interest

We are interested in building a Lean4 library which contains the following objects:

1. Rooted trees - planar, non-planar, labelled and unlabelled.
2. Hopf algebras over rooted trees - BCK, MKW etc and their duals. Characters over these Hopf algebras.
3. Series expansions - Butcher series and Lie-Butcher series.
4. Numerical methods - Runge-Kutta schemes, commutator-free methods etc, and their B-series or LB-series.

And also (only after the above are done):

5. Rough path theory - the definition of rough paths, geometric rough paths and branched rough paths.
6. Signatures, log-signatures, branched signatures and branched log-signatures.
7. Series expansions of rough differential equations (RDEs) in terms of the (branched) signature.
8. Numerical solvers for RDEs, including the log-ODE method.
9. And other results in Rough Path theory which will help to test the formalisations above. In particular, see https://arxiv.org/abs/2404.06583 and https://arxiv.org/pdf/math/0610300.

**Note (2026-07):** the tree-free part of items 5–9 — the sewing lemma, word
signatures/log-signatures, geometric rough paths and the geometric log-ODE
method — now lives in the standalone sibling project **LeanRoughPaths**
(`../lean-rough-paths`), which this repository requires via Lake. Branched
rough path theory (forest-indexed, built on the BCK Hopf algebra) remains
here under `BSeries/RoughPaths/`.


## Known theorems

Once the core objects are in place, we should formalise some known theorems. Of particular interest are Butcher's results concerning Runge-Kutta schemes, which can be found in Butcher_numerical_methods_book.pdf.

We should also aim to formalise the following papers: https://arxiv.org/abs/2507.21006 and https://arxiv.org/abs/2509.20599.

## Generality of results

When proving theorems, you should aim to keep results general if possible. For example, you may consider proving that the B-series of the true solution to an ODE has coefficients equal to the reciprocal of the tree factorial 1/\tau!. In which case you should aim to prove this for all trees \tau, rather than just proving it up to order 2, then order 3 etc. Proving it up to finite orders is not general enough in this case.

If you have initially proven a weak version of a theorem, but then followed it up with a strictly stronger version of the theorem, you should delete the original weak version to keep the repo clutter-free. Aim to remove dead code where possible.

## Repo structure

You are encouraged to re-structure the repo as work progresses to keep it clean and maintainable. Do not be afraid to rename files, move around large chunks of code etc in the name of maintainability and readability. Such restructures are encouraged. Make sure to have a nice folder structure rather than everything in the same folder.

## Verification

When implementing core definitions, objects or theorems, you are encouraged to check the formalisation by formalising simple results which follow from the defintion/object/theorem to check that the formalisation is correct.

## Mathlib

We must use the latest version of Mathlib in our project.

## Lean 4 notation

Lean 4 files may use standard Unicode notation and symbols. Do not apply a blanket ASCII-only rule to Lean code.

## Proofs

When proving a known theorem, you must try to follow the existing proof as closely as possible - do not try to invent your own proof. Once you have a finished proof, you are encouraged to golf it when possible. Comments explaining the proof or providing a citation to a paper where it originates are encouraged, but please keep these brief.

## Git rules

You are encouraged to commit and push whenever you make substantial progress. Keep the commit messages short one-liners.
