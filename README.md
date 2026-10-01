# Border's finite auction feasibility theorem

Lean formalization of the finite-type, single-item feasibility characterization
in Kim C. Border's *Reduced Form Auctions Revisited*, Theorem 7, and its
independent-prior corollary.

Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz.

For a finite bidder type `ι`, heterogeneous finite type spaces `T i`, a
nonnegative normalized joint prior `μ`, and an interim rule `q i a ∈ [0,1]`,
the theorem proves that an allocation exists exactly when, for every collection
of bidder-specific subsets `S i`,

\[
\sum_i\sum_{a\in S_i}\mu_i(a)q_i(a)
\leq \sum_{t:\exists i,\;t_i\in S_i}\mu(t).
\]

The allocation is a function `x t i` of the full profile. It satisfies
`0 ≤ x t i` and `∑ i, x t i ≤ 1` at **every** profile. Thus it allocates at most
one item and permits withholding; each individual probability is at most one.
No independence assumption appears in the correlated theorem.

The public theorem uses weighted equality
`interimMass μ x i a = marginal μ i a * q i a` at every type. A separately
proved equivalence connects this to conditional equality on **positive
marginal support**. Interim values at null types remain arbitrary within
`[0,1]`, as in the paper. Division by zero does not impose a condition there.

For independent, possibly different distributions `p i`, with each distribution
nonnegative and normalized, the right side becomes
`1 - ∏ i, (1 - ∑ a ∈ S i, p i a)`. The marginal and complement-event
factorization identities are proved, rather than assumed.

There are no payments, incentive compatibility requirements, deterministic
implementation claims, symmetric-auction restriction, infinite type spaces,
or claim to formalize every result in the paper. Empty finite bidder spaces
are permitted by the binders; no extra nonempty hypothesis is hidden.

## Proof and source map

| File | Content |
| --- | --- |
| `Border/Auction.lean` | Joint priors, marginals, allocation and feasibility definitions |
| `Border/WeightedHall.lean` | Finite threshold decomposition of all cut inequalities |
| `Border/Flow.lean` | Fractional Hall sufficiency from compact convex separation; cut necessity |
| `Border/Theorem.lean` | Bidder-type cut equivalence and full correlated-prior iff |
| `Border/Support.lean` | Null fibers, support-conditional equivalence, individual probability bound |
| `Border/Independent.lean` | Rectangle factorization, product marginals, independent corollaries |

The sufficiency proof forms the compact convex image of real-capacity flows.
A separating linear functional would have a larger value on the proposed
demand than on every feasible flow. Greedy allocation attains that functional's
support value, including the option of withholding. The finite threshold
lemma bounds nonnegative demand by that value using the cut inequalities,
contradicting separation. This is a complete proof for real probabilities,
without assuming a flow theorem or restricting probabilities to rationals.

`Challenge.lean` is a compact, self-contained Mathlib-only comparison contract.
Its ten genuine definitions retain their exact library bodies. The six selected
theorems retain their full statements, with deliberate `sorry` placeholders only
in these named Challenge theorem proofs, as permitted by the official comparison
policy. **All complete proofs remain in the library and `Solution.lean`**, with
no placeholders or extra axioms. The comparator checks the Challenge statements
against Solution; axiom auditing and all three kernels validate Solution proofs.
The implementation helpers remain in the distinct `Border.Implementation`
namespace; Challenge imports no project-local proof module.

Generate the contract with `python3 scripts/make_challenge.py` after editing the
library. The generator copies definitions and selected theorem headers directly
from the library, and the package checker restricts placeholders to those six
named Challenge statements. A compact contract avoids emitting the full helper
proofs and their repeated proof-state panels in the rendered statement page.
See `evidence/compact-challenge.md` for the reproduced size failure and the
validated replacement. The full mathematical scope and proof implementation
are unchanged.

## Build and verification

Pinned Lean: `leanprover/lean4:v4.35.0-rc2`.
Pinned Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
The committed manifest pins the transitive dependencies.

With [elan](https://github.com/leanprover/elan) installed:

```sh
lake update
lake exe cache get Mathlib.Analysis.LocallyConvex.Separation \
  Mathlib.Analysis.Normed.Module.FiniteDimension Mathlib.Tactic \
  Mathlib.Data.Fintype.Pi Mathlib.Algebra.Order.BigOperators.Group.Finset \
  Mathlib.Basic.Real.Basic
lake build
lake env lean Audit.lean
```

For the complete comparison replay, clone the official policy repository at
`65f0154ed776cd26c224254aa57b379137f28b0d`, set
`PALOMAR_SUBMISSION_DIR` to its absolute path, and run `./scripts/verify.sh`.
It validates the authored Comparator configuration with the official parser
and uses an execution-only temporary configuration for the bundled NanoDa and
con-ron kernels, alongside Lean's default kernel. The authored JSON contains
no submitter-provided external kernel commands. On macOS Comparator runs
without its Linux sandbox; hosted Linux CI uses bubblewrap.

Verification evidence and its precise source hashes are in `evidence/`.
GitHub Actions independently builds and compares the pushed source on Linux.
It also runs the pinned accepted-Challenge renderer and sanitizer under bubblewrap
and preserves the rendered size, source hashes, and bounded render artifact.
These are proof and package checks, not a Palomar submission or registration.

## Provenance

Primary source: [CaltechAUTHORS record and PDF](https://authors.library.caltech.edu/records/4f7kp-cze06).
That PDF is the September 2003 working paper, whose Theorem 7 and reduced-form
definition underlie the 2007 journal article:
Kim C. Border, *Economic Theory* **31**, 167–181,
[doi:10.1007/s00199-006-0080-z](https://doi.org/10.1007/s00199-006-0080-z).
The formalization uses a separately developed fractional Hall argument rather
than transcribing the paper's dual matrix calculation.

AI assisted source inspection, proof development, package preparation and an
independent mathematical/source review. All proofs require actual compilation
and kernel validation; model review alone is not proof verification. No human
mathematical review or author endorsement is claimed. See `formalization.yaml`
and `evidence/independent-review.md` for the review scope.

BSD-3-Clause; Mathlib and toolchain dependencies retain their own licenses.
