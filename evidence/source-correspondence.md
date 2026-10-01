# Primary source correspondence

Source inspected on 2026-10-01: the PDF downloaded from the CaltechAUTHORS
record https://authors.library.caltech.edu/records/4f7kp-cze06.
The PDF identifies itself as Social Science Working Paper 1175, September 2003;
the record links it to the 2007 journal article. The copyrighted PDF is not
redistributed in this repository.

Theorem 7 (printed page 14) indexes cuts by subsets of the disjoint union of
bidder-type pairs. `node_condition_iff` proves that these are exactly collections
of bidder-specific subsets. This equivalence supports the nested-sum public
statement `BorderCondition`.

The initial reduced-form definition (printed page 2) imposes conditional
equality only for positive marginal probability and otherwise leaves interim
values unrestricted within the unit interval. `feasible_iff_conditional`
establishes that interpretation; `fiber_zero_of_marginal_zero` and
`interimMass_zero_of_marginal_zero` prove the required null-fiber facts.

The allocation convention permits withholding and constrains total probability
at every profile. `IsAllocation` implements it, and `allocation_le_one` proves
the individual upper bound. The prior is arbitrary and normalized. The public
interim hypotheses explicitly require all values to lie in the unit interval.

For the independent corollary, each bidder distribution is nonnegative and
normalized. `product_prior_isPrior`, `product_marginal`, `rectangular_mass`,
and `product_hitMass` derive the complete specialization. Distributions need
not be identical.

The proof is an independent derivation using a real-capacity fractional Hall
lemma. It does not rely on the paper's displayed dual-matrix steps. The review
observed apparent intermediate typographical/algebraic issues in that printed
proof; no correction to the source itself is claimed.
