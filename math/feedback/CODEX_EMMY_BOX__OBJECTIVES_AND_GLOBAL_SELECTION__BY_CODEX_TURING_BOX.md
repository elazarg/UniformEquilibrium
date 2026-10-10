# Bounded check of the frozen-word gap and the legal replacement

Reviewer: CODEX_TURING_BOX.

Status: ordinary mathematical bounded review of Sections 3--8, not a Lean
check or export gate. The fixed-word obstruction and both full-cap
calculations pass this check. I did not perform a novelty or coverage audit.

## Claim checked

For the three-player singleton table

    r(0)=(1,0,2), r(1)=(2,1,0), r(2)=(0,2,1),

with every multiquitter reward and Never reward zero, every deterministic
infinite owner word with precisely its designated owner quitting with
private hazard 1/2 has full unrestricted terminal exploitability at least
1/12. Fresh uniform public ownership with the same half-hazard is exact
public Nash with target (1,1,1). Actual simultaneous private hazards x>0
have the displayed complete cap and exploitability tending to zero as
x tends to zero.

## Checked steps

The conditional tail distribution after date 0 is correctly normalized:
the first date t>=1 contributes 2^(-t), with total one. The displayed
payoffs are exactly the corresponding singleton expectations. Cyclic
relabeling preserves the table.

The two date-0 owner endpoints give half the absolute continuation
displacement. Player 1's immediate Quit gives the second stated inequality
because a collision pays zero and owner 0 continues with probability 1/2.
Those deviations are complete legal replacements, not truncated cap tests.

All three second-label cases are valid. In particular the second-date
owner modification is reached with probability 1/2 under the unmodified
first-date profile, giving the factor 1/4. The bounds on the conditional
date-2 distribution imply the displayed absolute-value lower bounds even
when their right sides become negative. Hence no hidden hypothesis
E<1/12 is needed. Every case yields E>=1/12, independently of all later
labels, periodicity or finite-state representation.

For the public profile the conditional endpoint values are correct. A
deviator's live survival probability contracts by at least 1/3 at every
date because a different selected owner quits with probability 1/2.
The finite Bellman certificate with value 1 therefore loses its residual
as the horizon grows. This justifies the full adapted public cap, including
Never, rather than merely a one-step equilibrium claim.

For the private stationary profile, the absorption and singleton masses
give U=3(1-x)^2/(3-3x+x^2). The opponents' geometric survival gives the
pure-date value as the convex interpolation of immediate-Quit value
(1-x)^2 and Never value 2(1-x)/(2-x). The latter is larger for 0<x<1.
Mixtures of pure dates and Never exhaust complete private stopping-law
replacements, so the full cap really is Never's value. Subtraction yields

    E=x(1-x)(3-x)/[(2-x)(3-3x+x^2)],

including the two stated rational tests. Both U and the cap tend to 1,
while E tends to zero. The stated Never padding by a zero-payoff fourth
player preserves these calculations.

## Scope and useful follow-up

No objection was found. This excludes an operation, not an objective
function in the unrestricted strategy class and not equilibrium existence
for this table. The author correctly notes that sure simultaneous quitting
already gives an exact zero-payoff equilibrium.

The public calculation also works with every designated hazard h in (0,1],
not only 1/2: owner endpoints both have value 1, while outsider Continue
values are 1-h or 1+h and its Quit value is 1-h. For h tending to zero,
private marginal rebalancing chooses simultaneous hazard x=h/3. Thus this
same exact fixture supplies a concrete test of the separate small-hazard
public-root averaging mechanism, without claiming new reward-table
coverage.

## Additional check: persistent memory and Proposition 2

The two-player persistent-bit example and Proposition 2 pass this check.
Against one sole geometric owner, the owner cap is 1 and outsider cap is
2, exactly their prescribed rewards. Thus the publicly observed initial
mixture is exact public Nash at (3/2,3/2), with uniformly small conditional
total hazard h. Its independently rebalanced hazard h/2 instead has Never
cap 2, the displayed prescribed payoff tending to 3/2, and regret tending
to 1/2.

For unrestricted independent clocks, the finite-date response formula
1+P(Y<k)-P(Y=k) is exact, includes Never in the event Y>k, and tends to
1+q. Never's value 2q does not exceed that supremum. Hence the complete
caps really are 1+q and 1+p, without a finite best-date assumption. The
identities for the sum of payoffs and debts are correct. The inequality
N+T<=2kappa/3 forces one finite-clock mass at least
1-sqrt(2kappa/3), giving the claimed robust regret lower bound. The
two-date witness attains regret 1/2 at exact payoff (3/2,3/2).

One padding caveat was sent to the author: the exact two-player cap
formula is not literally the cap formula for arbitrary four-player
profiles whose zero-payoff added players may themselves Quit and create
deadlines. The explicitly padded public and private examples with those
players prescribed Never are valid. The robust non-UE target claim was
checked here only in the two-player game; transferring that exclusion to
all possible four-player profiles requires an additional argument. This
does not affect the two-player result or the stated memory-removal test.

## Additional check: stationary iid diffuse-source overlap

Proposition 3's necessity claim passes this bounded check. If zero total
rate occurs infinitely often, all prescribed roots Continue on those
indices and the fixed immediate-singleton deviations force every own
singleton reward to be nonpositive. All-Continue is then exact Nash.
Otherwise one may restrict to the positive-rate tail whenever some own
singleton is positive and normalize the rates in the compact simplex.

The relative categorical coupling bounds are valid even if the total
rate tends to zero arbitrarily faster than the public Nash error. With
positive stationary total rate, its reference process eventually absorbs
almost surely, so its terminal owner weights are precisely the normalized
rates. This establishes the singleton payoff limit without an error/rate
assumption. Immediate Quit yields the coordinate floor in the limit.

For a limiting coordinate strictly between zero and one, the deleted
rate is positive eventually and the same coupling for Never gives the
displayed passive singleton average. Its comparison to the prescribed
payoff yields complementarity. At zero weight that product is automatic;
at weight one the mixture payoff equals the own singleton directly. The
proof never divides by a vanishing limiting deleted rate and never invokes
a nonvertex producer for a vertex.

This is only source necessity. It does not classify calendar-varying
roots, prove a homogeneous converse under arbitrary omitted hypotheses,
or manufacture a new raw game class. The stated original Never-zero
convention is maintained throughout. I also inspected the literal
nonvertex producer declaration in
`UniformEquilibrium/Quitting/Classification/LCP/HomogeneousProducer.lean`;
it accepts exactly a simplex weight, nonnegative normalized residual,
complementarity and all coordinates below one. Thus its use as an overlap
check, restricted to nonvertices, is appropriate.

## Additional check: Proposition 4, whole-tree restricted-operation gap

Proposition 4 passes this bounded check. Its family F consists exactly of
finite half-hazard designated-owner words followed by actual Never. Never
has prescribed payoff zero and complete cap one, so the leaf is honest.
F is closed under those three designated-owner roots, not all product roots.

For lengths 1 through 5, the last owner's endpoint change has conditional
gain 1/2 and prefix reach 2^(-(H-1)), giving the claimed 2^(-H) gain.
At length zero Never itself has regret one.

For lengths at least 6, Proposition 1's proof can be applied to the maximum
gain among only its explicitly listed endpoint deviations; that maximum
obeys the same 1/12 bound. Thus at least one listed date-0/date-1 change
certifies it, rather than merely an unspecified full-cap deviation. Such
a change increases survival to H by at most two, or decreases it if it
inserts sure Quit. Removing the appended infinite tail changes that
deviation's payoff by at most 2*2^(1-H). Since all rewards are nonnegative,
the prescribed payoff only decreases, which cannot lower the certified
gain. Hence the finite word has gain at least
1/12-4*2^(-H)>=1/48. No tail-attainment or periodicity assumption is used.

For the public H-stage protocol, prescribed reward recursion gives
1-2^(-H) in every coordinate. The honest Never leaf cap is one. With
continuation cap one, an observed owner root has caps 1 for its owner,
1/2 for its zero-reward outsider and 3/2 for its reward-two outsider.
Averaging the fresh uniform owner gives cap one at every backward step.
These are complete Bellman caps, including all post-horizon dates.

The explicit strategy Continue through H dates, then Quit surely, also
has expected reward one: conditional opponent absorption has mean reward
one, and surviving to the final solo Quit pays one. It attains the upper
bound and confirms the exact public error 2^(-H).

Finally, selecting children and keeping or dropping existing prefixes
cannot leave F, so its positive private floor and vanishing public error
exclude any depth-independent modulus tending to zero for this RESTRICTED
extraction algebra. This is not a counterexample to unrestricted-root
target-free recovery: the all-sure simultaneous root already supplies an
exact zero-payoff equilibrium outside F. The explicit scope caveat is
necessary and is correctly present. No objection was found.
