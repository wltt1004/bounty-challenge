# Sources and handoff

## Target

- Erdős problem 1004: https://www.erdosproblems.com/1004
- Formal Conjectures statement `Erdos1004.erdos_1004` and the definition
  `Erdos1004.IsDistinctTotientRun`:
  https://github.com/google-deepmind/formal-conjectures/blob/379fc0298dc146df549e7061c3ede0353a5bb51f/FormalConjectures/ErdosProblems/1004.lean
- The contribution is checked against Formal Conjectures commit
  `379fc0298dc146df549e7061c3ede0353a5bb51f`, the commit pinned by the target pool.

## Mathematical sources

- S. W. Graham, J. J. Holt, and C. Pomerance, *On the solutions to
  φ(n) = φ(n+k)*, Number Theory in Progress, vol. 2 (1999), 867–882:
  https://math.dartmouth.edu/~carlp/phi.pdf
- Eric Li, *Rank Amplification for Shifted Equal Values of Euler's Totient
  Function*, arXiv:2606.23681v2:
  https://arxiv.org/abs/2606.23681
- Eric Li's Apache-2.0 Lean formalization accompanying that paper, pinned here
  at commit `5f06df5c7d745e0cfb7718556159a8f3d704f6c9`:
  https://github.com/ericlisg/RankAmplificationTotient/tree/5f06df5c7d745e0cfb7718556159a8f3d704f6c9

The same-prime-support affine construction in `GHPDiagonal` is an adaptation of
the Graham–Holt–Pomerance diagonal described in the paper and of its organization
in the external formalization's `Definitions.lean`, `Elementary.lean`, and
`DiagonalTransfer.lean`. The definitions and proofs here are rewritten as a
self-contained target-facing API in the pinned Formal Conjectures environment.
In particular, this contribution does not import the external repository.

The finite collision-cover formulation, the exact complement identity, the
weighted first-moment union bound, and the positive/negative target interfaces
are original formal integration for Erdős 1004.

## Mathlib declarations used

The file uses the existing `Nat.totient` API, principally
`Nat.totient_mul`, `Nat.totient_prime`, and
`Nat.totient_eq_mul_prod_factors`, together with finite-set cardinality and
interval lemmas. Current documentation is available at:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Totient.html

## What the contribution provides

The central checked handoff is the following chain.

1. `isDistinctTotientRun_iff_not_hasShiftedTotientCollision` rewrites the target
   predicate exactly as absence of a positive-shift equal-totient pair in the
   run interval.
2. `mem_collisionCoveredStarts_iff` identifies failed starts with a finite union
   of spoiler intervals, while
   `distinctTotientRunStarts_eq_sdiff_collisionCoveredStarts` gives the exact
   finite complement.
3. `collisionCoveredStarts_card_le_weightedCollisionSum` proves the weighted
   union bound
   `#covered ≤ ∑_{1 ≤ h < K} (K-h) P(x+K,h)` inside Lean.
4. `exists_isDistinctTotientRun_of_weightedCollisionSum_lt` turns any future
   analytic upper bound making that sum smaller than `x+1` into the desired
   finite run existence statement.
5. `ghp_totient_eq` proves the general same-support affine equal-totient family,
   and `not_isDistinctTotientRun_of_ghp` connects it directly to failure of the
   target run predicate.
6. `classical_h_two_totient_eq` formalizes the classical shift-two prime-pair
   specialization, and
   `erdos_1004_false_of_frequently_classicalHTwoCoverage` turns a future local
   coverage theorem for that family into a refutation of the exact target.
7. `erdos_1004_of_eventually_weightedCollisionSum_lt` and
   `erdos_1004_false_of_frequently_allStartsHaveCollision` are end-to-end
   interfaces matching the two possible target modes.

Thus later work can focus on the genuinely analytic step—bounding the weighted
collision count for the positive direction, or proving frequent local coverage
for the negative direction—without rebuilding the finite combinatorics,
structured-collision arithmetic, or filter-level connection to the statement.

## Scope and non-claims

This is a partial proof contribution, not a claimed solution or refutation. It
proves the exact reductions and the structured collision family, but it does not
assert the missing asymptotic collision-count or local-coverage estimate.

At preparation time, the public `contributions/erdos-1004` index contained no
published contribution, so `parents` is empty. This should be rechecked against
current `main` immediately before promotion.

## Tool assistance and responsibility

The Lean development and documentation were produced with assistance from
OpenAI GPT-5.6 Pro, then kernel-checked against the pinned target environment.
The human author who promotes and signs the contribution remains responsible for
its correctness, provenance, licensing, and claims.
