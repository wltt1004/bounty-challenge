# Sources and lineage

## Target

- Formal Conjectures, Erdős Problem 1004, pinned source:
  https://github.com/google-deepmind/formal-conjectures/blob/379fc0298dc146df549e7061c3ede0353a5bb51f/FormalConjectures/ErdosProblems/1004.lean
- Conjectures task bundle, pinned pool revision:
  https://github.com/conjectures-io/conjectures-tasks/tree/4bd1d01dd6193eec6b48eb6176ebdae9aa76a384/pool/tier-1/erdos-1004-formalized

## Mathematical sources

- S. W. Graham, J. J. Holt, and C. Pomerance,
  *On the solutions to φ(n) = φ(n+k)*, in *Number Theory in Progress*,
  Vol. 2, de Gruyter (1999), pp. 867–882:
  https://math.dartmouth.edu/~carlp/phi.pdf

  The declarations `diagonalGCD`, `diagonalA`, `diagonalB`, `IsGHPParameter`,
  and `ghp_totient_eq` implement the same-support affine prime-pair
  construction behind the Graham–Holt–Pomerance diagonal.

- Eric Li, *Rank Amplification for Shifted Equal Values of Euler's Totient
  Function*, arXiv:2606.23681 (2026), and its Lean formalization at commit
  `5f06df5c7d745e0cfb7718556159a8f3d704f6c9` (Apache-2.0):
  https://arxiv.org/abs/2606.23681
  https://github.com/ericlisg/RankAmplificationTotient/tree/5f06df5c7d745e0cfb7718556159a8f3d704f6c9

  The elementary same-support coefficient arithmetic in this contribution is
  adapted from the formalization's `Definitions.lean`,
  `DiagonalArithmetic.lean`, and diagonal totient lemmas. The target-specific
  run/collision layer, exact finite cover, weighted union bound, and asymptotic
  bridges are new Lean integration for Erdős 1004.

- Mathlib's Euler-totient API, pinned through Mathlib/Lean 4.27.0:
  https://github.com/leanprover-community/mathlib4/blob/a3a10db0e9d66acbebf76c5e6a135066525ac900/Mathlib/Data/Nat/Totient.lean

## Original contribution and concrete use

The contribution supplies:

1. the exact local equivalence
   `isDistinctTotientRun_iff_not_hasShiftedTotientCollision`;
2. exact finite sets of shifted collisions, spoiled starts, the complete
   collision cover, and the complementary good-start set;
3. the exact identity
   `good starts = (x + 1) - collision-cover cardinality`;
4. `collisionCoveredStarts_card_le_weightedCollisionSum` and the direct
   sufficient criterion `weightedCollisionSum x K < x + 1` for a desired run;
5. exact reformulations of the positive target as eventual non-full coverage
   and of the negative target as frequent full coverage;
6. the target-local GHP construction and the classical shift-two family
   `φ(2(4t+1)) = φ(2(4t+1)+2)` when `2t+1` and `4t+1` are prime.

A later positive proof can target
`erdos_1004_of_eventually_weightedCollisionSum_lt` or the exact cover criterion
`erdos_1004_iff_eventually_collisionCoveredStarts_card_lt`.
A later refutation can target
`erdos_1004_false_iff_exists_frequently_collisionCover_full`, or establish
frequent coverage by the shift-two/GHP subfamilies and apply the supplied
refutation interface.

No complete resolution of Erdős 1004 is claimed. No unproved analytic estimate,
prime-pair gap assertion, source conjecture theorem, `sorry`, `axiom`,
`native_decide`, or executable proof shortcut is used.

## Formal verification

The file was checked against:

- Lean `v4.27.0`;
- Formal Conjectures commit
  `379fc0298dc146df549e7061c3ede0353a5bb51f`;
- Mathlib commit `a3a10db0e9d66acbebf76c5e6a135066525ac900`;
- the official `conjectures-contribution` preflight at canonical main.

OpenAI GPT-5.6 Pro assisted with the mathematical audit, Lean development,
documentation, and CI iteration. Every submitted theorem is kernel checked.
