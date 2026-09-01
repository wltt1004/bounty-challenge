# Erdős 1004 partial-contribution submission handoff

## Prepared contribution

**Target:** `erdos-1004`

**Title:** `Exact collision-cover reduction, first-moment bound, and GHP obstruction API for Erdős 1004`

**Kind:** `partial-proof`

**Mode:** `either`

**Artifacts to promote:**

- `lean-test/Erdos1004ContributionTest.lean` as `script.lean`
- `contribution-draft/sources.md` as `sources.md`
- `contribution-draft/draft.json` as `draft.json`

The Lean file has been compiled in GitHub Actions against Formal Conjectures
commit `379fc0298dc146df549e7061c3ede0353a5bb51f`, including the exact
`FormalConjectures.ErdosProblems.«1004»` module.

## Wallet-bound promotion and submission

Run these commands on the machine containing the Bittensor wallet. Do not use
`--no-reward`, because reward data is committed into the contribution id and
cannot be added later.

```bash
git clone --recurse-submodules https://github.com/conjectures-io/conjectures-contribution.git
cd conjectures-contribution
./install.sh

git pull --ff-only
git submodule update --init --recursive

contrib config set wallet_name <wallet>
contrib config set wallet_hotkey <hotkey>
contrib wallet show

contrib new erdos-1004 \
  --title "Exact collision-cover reduction, first-moment bound, and GHP obstruction API for Erdős 1004" \
  --kind partial-proof \
  --mode either

cp /path/to/bounty-challenge/lean-test/Erdos1004ContributionTest.lean \
  drafts/erdos-1004/script.lean
cp /path/to/bounty-challenge/contribution-draft/sources.md \
  drafts/erdos-1004/sources.md
cp /path/to/bounty-challenge/contribution-draft/draft.json \
  drafts/erdos-1004/draft.json

contrib promote erdos-1004
contrib check

gh auth login
CONTRIBUTION_DIR=$(find contributions/erdos-1004 -mindepth 1 -maxdepth 1 \
  -type d | sort | tail -n 1)
contrib submit "$CONTRIBUTION_DIR"
```

Before promotion, inspect `contributions/erdos-1004/index.md` after pulling the
latest `main`. If a materially overlapping contribution has appeared, add its
64-character id with a repeated `--parent` option when recreating the draft and
explain the delta in `sources.md`.

## Proposed pull-request title

```text
partial-proof(erdos-1004): exact collision cover, first moment, and GHP obstruction API
```

## Proposed pull-request body

```markdown
## Summary

This contribution formalizes the central finite reduction behind Erdős 1004.
It proves that a distinct-totient run is exactly a candidate interval containing
no positive-shift equal-totient collision, packages all failed starts as a finite
union of spoiler intervals, and proves the weighted first-moment bound

`#covered ≤ ∑_{1 ≤ h < K} (K-h) P(x+K,h)`.

It also formalizes the general Graham–Holt–Pomerance same-support affine
collision family, its classical shift-two prime-pair specialization, and
end-to-end interfaces matching both the positive and counterexample modes of
the exact target.

## Material handoff

A later positive proof can invoke
`erdos_1004_of_eventually_weightedCollisionSum_lt` after proving the analytic
weighted-collision estimate. A later refutation can invoke
`erdos_1004_false_of_frequently_allStartsHaveCollision`, or the more concrete
`erdos_1004_false_of_frequently_classicalHTwoCoverage`, after proving a local
coverage theorem. The finite combinatorics, structured-collision arithmetic,
and filter-level target plumbing are already checked.

## Verification

The single Lean artifact compiles against the target pool's pinned Formal
Conjectures commit `379fc0298dc146df549e7061c3ede0353a5bb51f`. It contains no
admissions, new axioms, unsafe declarations, metaprogramming, or forbidden
evaluation commands.

## Provenance

The GHP construction is attributed to Graham–Holt–Pomerance and to Eric Li's
Apache-2.0 formalization. The finite cover, exact complement, weighted union
bound, and target-facing integration are original to this contribution. Full
links and the tool-assistance disclosure are in `sources.md`.

## Scope

This is intentionally a partial proof contribution. It does not claim the still
missing asymptotic collision estimate or local collision-coverage theorem.
```

## Rubric evidence for maintainers

This is not a self-awarded score, but the checked evidence supports a high
recognition weight:

- **Target impact:** the contribution isolates and formalizes the central
  collision-cover subproblem and supplies complete sufficient interfaces for
  both target modes.
- **Generality and reuse:** the collision sets, spoiler intervals, exact cover,
  weighted sum, GHP family, and target interfaces are reusable separately.
- **Originality of the delta:** the elementary finite reduction is integrated
  with the target for the first time, and the external GHP idea is adapted into
  a self-contained pinned-environment API.
- **Verification and handoff:** declarations are documented, exact equivalences
  are proved, both directions have representative end-to-end use theorems, and
  provenance plus non-claims are explicit.

A plausible review target is weight 8 (impact 3, reuse 2, originality 1,
handoff 2), with a possible ninth point if reviewers regard the combined finite
cover/GHP integration as a substantial formalization insight. The final weight
is solely the maintainers' signed decision.
