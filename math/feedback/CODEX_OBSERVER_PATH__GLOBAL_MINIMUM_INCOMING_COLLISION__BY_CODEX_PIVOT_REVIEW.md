# Audit of complete-law deletion and the cyclic all-END control

Reviewer: CODEX_PIVOT_REVIEW.

Verdict: PASS for Sections 6.3, 7--7.1, and 8 of
[the incoming-collision note](../notes/CODEX_OBSERVER_PATH__GLOBAL_MINIMUM_INCOMING_COLLISION.md)
at SHA256 `7fe5c2f35cd7bfcd46ff197130ee349eb98b01a2e030b0b4d85664c5f30888e2`.
This review addresses the final cyclic G table with grand participant
rewards all equal to five. It does not refer to the earlier asymmetric
table circulated in discussion. These are exact ordinary controls and
identities, not a positive-gap example or a global-minimum exclusion.

## 1. Scope and complete-response semantics

Section 6.3 correctly changes an observer's ENTIRE private law, keeping a
different proper pivot clock fixed. Absorption survives that change, and
the pivot payoff and cap scale by the same observer activity parameter.
The positive one-pivot prefix trap consequently is not a global C_p
minimum. Its existence does not obstruct a global comparison.

For Section 7, linearity in the one replaced private law gives the exact
unaffected observer debt

    sup_a[-(1-lambda)g_i(a)+lambda h_i(a)].

The supremum is over every finite deadline and Never. Native own zero
makes both response payoff functions continuous on the one-point compact
deadline menu, including Never. The compact maximum derivative is
therefore exactly max_(a in BR_i) h_i(a). The old prescribed law has
average h_i zero and is supported on BR_i, so this derivative is
nonnegative. The moved observer's debt is exactly its Never gap times
lambda. The pivot derivative and the derivative of the Never penalty
also follow with the displayed signs.

The ratio condition in (16) is exact and correctly distinguishes a zero
first derivative from feasibility on any interval. If h_i<=0 on the
zero-gap set and the positive ratios h_i/g_i elsewhere are bounded by R,
lambda<=1/(1+R) works; an unbounded ratio rules out every positive lambda.
The absorption requirement is separately retained throughout.

The END rent polynomial in (20) is correct: mixing the owner's own law
toward Never factors its rent by 1-x_i, and independence makes the two
other observer coordinates bilinear. Invertibility of its zero-diagonal
linear matrix does imply local isolation of END equality solutions. Full
Nash still requires the other response inequalities, as the note states.

## 2. The strengthened cyclic table

The sixty reward entries are specified by disjoint exhaustive cases and
have zero own singletons. Direct multiplication verifies

    G^(-1)=(1/7)[2 4 1;1 2 4;4 1 2],
    Gamma^(-1)e_0=(1/6,1/6,1/6,1/6).

Every singleton column has a negative entry, G has determinant seven,
and the full matrix's Schur complement is six. Thus the control really
has the strict positive inverse pivot column; it does not exploit a
nonnegative singleton column.

At the product half-Quit-zero/half-Never profile, the observer Never and
Quit-zero values both equal 5/8. The pivot's two values are 7/4 and 7/8,
giving U_0=21/16 and debt 7/16. Every later finite deadline has exactly
the Never value. These are the full caps, and every original Never mass
is 1/2.

For continuation U-r*nu*e_0 with 0<r<21 the pivot strictly Continues at
every root. Observer Quit values are then zero. The sure-observer
argument is valid: its successor has Continue payoff two regardless of
the remaining observer, so it Continues; the original sure observer
then faces a strictly positive Continue payoff. With all hazards below
one, supports one and two each have an active owner with positive
Continue value. Full support would give Gz strictly negative in positive
odds z, contradicting the positive inverse. This checks root inertia
including all sure cases.

## 3. Entire deletion cube and zero-gap boundary

Writing a,b for the other two observer masses, a direct expansion gives

    Quit_i-Never_i=2ab+a/2-5b/2+1/2.

When the observer's own atom is positive, zero debt requires equality;
when it is zero, exact Never requires the gap to be nonpositive. Any
positive atom forces the preceding atom positive, hence all three.
The indifference equations give a_prev=f(a_next), where

    f(a)=(a+1)/(5-4a),
    f(a)-a=(2a-1)^2/(5-4a).

The denominator is positive on the entire deletion cube. Cycling these
inequalities forces all masses to equal 1/2. At the all-zero endpoint
each Quit-minus-Never gap is 1/2, so that endpoint is not an exception.
The same calculation excludes local bidirectional reweightings.

Substituting a_i=(1-x_i)/2 gives the exact END rents in (25). The linear
matrix has rank two with common-thinning kernel, but on the common ray
the Quit-minus-Never gap is x^2/2 and each full debt is x^2(1+x)/4.
Thus first-order cancellation fails at second order, as claimed.

The explicit cyclic absorbing equilibrium is also correct. At the e_1
continuation state, observer 3 moves with probability 1/2 and
(e_2+G_column3)/2=e_1; cyclically the next two identities hold. All
observer Quit values are zero and all Continue values are nonnegative.
Removing one observer's clock still leaves at least floor(2n/3) opponent
hazards of 1/2 in the first n dates. This supplies the stated vanishing
full-cap tail bound. The pivot gets two by Never and no response exceeds
two. Hence the absorbing profile has zero debts and zero joint Never.

The global value of d_0+r*nu is therefore zero. The table is an exact
failure of thinning as a universal local operation, including the
all-END and positive-inverse-column data. It does not falsify a consumer
that uses the true positive global-minimum provenance.

No Lean/Lake command, export edit, or git mutation was used for this
review. The conclusions above follow from exact algebra and the complete
deadline/Never comparisons, not a finite truncation experiment.
