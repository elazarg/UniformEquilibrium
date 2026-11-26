# Adversarial review of exact Nash nonattainment

Reviewer: CODEX_COLLAR_ADVERSARY.

**Mathematical verdict: PASS.** The unrestricted exact-Nash nonattainment
theorem and the zero-debt semantic-closure corollary have no unresolved
mathematical objection in this review. This is ordinary mathematics, not a
Lean verification. No other review of this artifact was read.

Reviewed artifact:
[CODEX_NEGATIVE_CAPS__EXACT_NASH_NONATTAINMENT.md](../notes/CODEX_NEGATIVE_CAPS__EXACT_NASH_NONATTAINMENT.md).
Exact SHA256:

    21398bb9acd2987538cfde743dbdd0969ab6929806a4baafa009746b0ccc5646

## Exact scope

For the stated complete calibration there is one positive threshold such
that every independent choice of the three strictly positive premiums
below it has no exact terminal Nash profile. Profiles may have arbitrary
infinite supports and Never masses. The threshold imposes no premium-ratio
restriction. The argument additionally proves nonnegative native coordinates
at every zero-debt point in the closure of actual payoff/cap pairs.

The result does not exclude approximate Nash profiles at every accuracy,
does not prove a positive unrestricted exploitability gap, and does not
settle Fin4. The three-diffuse-flow theorem gives uniform equilibria on
the ray (e,h1,h3)=(beta,beta/10,beta) for sufficiently small beta. The native
continuation used here is original payoff minus one, so original Never zero
has native bookkeeping value minus one. That convention is essential to
the final contradiction and is explicitly stated.

## Semantic reduction and finite prerequisites

An exact Nash profile passes exact Nash to every conditional tail reached
with positive probability: a profitable replacement there can be spliced
after that date and increases initial payoff by positive reach times its
conditional gain. Before a possible first sure root, its one-step root
is Nash against an actual continuation, including an arbitrary prescribed
off-path continuation if necessary. Therefore the sure-root census rules
out that first root and all finite dates have positive reach.

With every hazard below one, Continue must be optimal for every player.
Each positive Quit hazard must also be optimal. This gives exactly the
displayed relation(2), with continuation coordinates in[-3,10] and
coordinate2 at most2. The closed form of the active condition is
q_i(C_i-Q_i)=0; thus the relation survives all compactness arguments.

I checked the entire sure-owner census in Section8 of the unequal-premium
export. Its cases x=1, y=1, z=w=1, z=1 alone and w=1 alone exhaust the
possibilities, including zero coordinates. Only the lower continuation
bound C2>=-3 is used. The explicit parameter box contains a uniform small
cube of independent premiums. Exact symbolic substitution reproduced E3,
the z=1 boundary expression g2+3H2, and the two free-face polynomials.

I also checked the zero-premium nonnegative-input certificate used in(3).
Its four inequalities follow from the four active equalities even at
zero or unit limiting hazards. Exact rational Bernstein conversion
reproduced the four minima

    313/144, 5/9, 2, 55/36.

The L<=0 branch separately forces the zero root; no strict interior-root
assumption is hidden in this prerequisite. The final activity theorem is
used only after all continuation coordinates have been proved nonnegative
and with the required upper bound C2<=2.

## The zero-premium infinite-sequence argument

1. A negative coordinate forces three positive opponent hazards. Only
   coordinates1 or3 can be negative at zero premiums. Hence a negative
   phase has support012,023 or full support. This uses the Quit lower
   bound C_i>=Q_i, without assuming that the negative player quits.

2. For support012, the active equations yield z>=3y and y>=x, while
   both coordinates1 and3 of the next vector are negative. The next
   phase must be full. Its zero coordinate2 forces x=y=s at the current
   phase. Substituting the next full output gives X>5Y and then
   W>=2(X-Y)>8X/5. The supposedly negative coordinate is exactly

       H*Y*Z*[10W-(1-s)X],

   which is positive. All divided factors are positive; the equations
   also exclude a unit current hazard.

3. For support023, the analogous inequalities are z>=3w and w>=2x.
   Both next coordinates1 and3 are negative, so the next phase is full.
   Its zero coordinate2 forces w=2x=2s and s<1/6. The two active
   equations imply X>8W, and the next row2 implies Y>15X/16. The
   supposedly negative coordinate is exactly

       2s+2H0*Z*W*[5Y-(1-s)X]>0.

4. Every negative phase is therefore full. If its next vector were
   nonnegative, the zero-premium certificate would force its root to be
   zero, a contradiction. Thus any negative phase supplies an infinite
   consecutive full-support chain, with K>0 throughout.

5. I rederived the two scalar recurrences and the identity
   D=30a squared-23a+6+(5a-1)b. The quadratic minimum is191/120.
   The argument excluding H1=0 works both below and above a=1/4;
   it also gives H0>0. For a>1/4, the exact quotient formula gives a
   strict decrease greater than1/20. The two intervals below1/4 are
   forward invariant by the stated separate estimates. Once a<=1/4,
   K grows by at least9/8 at every step, contradicting its bound2.
   These conclusions concern arbitrary bounded infinite sequences, not
   only cycles or sequences realized by profiles.

## Uniform positive-premium extension

The first compactness argument is uniform over all bounded continuation
sequences and all premium ratios. If negative coordinates stayed bounded
away from zero as the maximum premium vanished, shift each sequence to
such a coordinate, choose its index along a subsequence, and use diagonal
compactness on the countable future coordinates. The closed relation(2)
would give a forbidden negative zero-premium sequence.

The second compactness argument also checks: at a negative phase only
supports012,023,013 or full are possible. Support013 is immediately
excluded by its row0 equality. For a fixed remaining support, the relevant
active equalities survive a limit even if some limiting hazards vanish.
The full case uses(3); the two proper cases force the zero root by their
displayed linear inequalities. Thus negative-phase activity tends to zero
uniformly, rather than merely along a chosen equilibrium family.

The bootstrap then removes all residual negativity. The full-support
estimate gives s<9delta from the exact coefficient83/30; the two proper
supports give the stated weaker bounds s<3delta and s<6delta. In
particular s<=12delta in every possible negative phase. Each negative
coordinate is bounded below by minus s cubed divided by nine. Taking
suprema gives delta<=192 delta cubed; delta<1/20 forces delta=0.
This handles coordinates that vanish arbitrarily faster than the premiums
and does not assume the supremum is attained.

## Final nonattainment and the semantic corollary

The activity theorem now permits player0 only alone. Under that restriction
every player's Quit payoff is strictly positive whenever an opponent acts.
A solo phase fixes its owner's current and next values at zero; this zero
propagates until a first different owner acts, contradicting the positive
Quit payoff. If no different owner ever acts, a negative singleton outsider
has strictly negative actual payoff, including the native Never value-1.
Thus there are no solo phases and player0 never acts.

Player2's actual native payoff then increases weakly down the tail. Each
positive player2 hazard requires another active owner and increases the
next value by a factor at least1/e. Since its first such value is positive
and the values are bounded by2, only finitely many such dates exist.
Afterwards its actual payoff is at most-1 on every terminal outcome and
on Never. This contradicts nonnegativity. This last step legitimately uses
actual realization; it is not applied to an abstract semantic chain.

For Section6, extracting first roots and bounded child pairs from actual
approximants gives the displayed continuous prefix identities. A zero-debt
parent has R_i+h d'_i=0 with both terms nonnegative. Thus its root is
fully Nash against the child caps. The sure-root census applies because
the child's coordinate2 is at least-e and at most2; hence h>0 and the
child also has zero debt. Iteration produces a bounded sequence satisfying
(2), to which the uniform nonnegativity theorem applies. When an actual
approximant has zero survival, undefined conditional laws can be chosen
arbitrarily off path: their affected coefficients vanish. No actual
realization of the extracted infinite semantic tail is inferred.

The cited exact-terminal and approximate-terminal semantic endpoints in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
were inspected statically, as were the full-response prefix declarations
in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean` and
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
No Lean commands ran. Exact symbolic checks supplemented the independent
proof rederivation; bounded numerical searches were not used as evidence
for nonattainment.
