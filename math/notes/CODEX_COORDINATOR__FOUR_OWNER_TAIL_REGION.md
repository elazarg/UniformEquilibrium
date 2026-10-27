# An open raw chamber forces either finite support or four infinite owners

Owner: CODEX_COORDINATOR.

This ordinary mathematical theorem concerns actual native ALL-END profiles,
not UE existence. It strengthens the benchmark's actual-tail reduction:
no positive absorbing gap, genericity or dispersion hypothesis is needed.

Here an actual profile is a product of four private laws on the natural
dates together with a separate Never label. The first nonempty quitting
coalition receives its native reward; if everybody chooses Never the
reward is zero. A unilateral response may replace an entire law, including
any finite deadline, Never, or any private mixture. The full cap B_i is
the supremum over this entire menu, U_i is the prescribed payoff, and
debt is B_i-U_i. ALL-END means that pure Never attains B_i. Infinite
support means infinitely many distinct finite dates of positive marginal
probability; it does not mean that the owner quits almost surely.

## Raw finite certificate

Fix a bounded native four-player quitting table Z with own singleton and
Never rewards zero. Write `Gamma_ij=Z_i({j})`, `J_ij=Z_i({i,j})` for i!=j,
and set both diagonals to zero. For a player subset S, weights l in R^4,
and a subset A of S whose current atoms are constrained to vanish, put

    c_j=sum_i l_i Gamma_ij, d_j=-sum_i l_i J_ij,
    C(S,A,l): c_j+max(d_j,0)<0 for j in S minus A,
               c_j<0 for j in A.                     (1)

This is a finite list of strict linear inequalities: each max condition
is equivalent to `c_j<0` and `c_j+d_j<0`.

Assume `Gamma_02<0<J_02` and, for some epsilon>0 and gamma in R, the five
following certificates hold:

| S | A | l in player order0123 |
|---|---|---|
|013|empty|(-9/10,1,0,19/20)|
|023|empty|(0,0,1/2,-1)|
|123|empty|(0,-1,0,1/2)|
|012|{1}|(1,1/2,0,0)|
|012|empty|(gamma,1+epsilon,0,1)|

The parameter gamma need not be positive: its row0 multiplier will only be
used at an exact observer contact. These conditions define an open
polyhedral region when epsilon,gamma are fixed. All thirty-two native
reward entries beyond own singletons, off-diagonal singletons and
participant pairs may vary arbitrarily, provided they remain finite.

**Theorem.** Every actual independent complete-law profile with positive
marginal Never masses, full caps equal to the pure-Never payoffs for all
players, and zero debts for observers0,1,3, has either no infinite-support
owner or all four infinite-support owners. Pivot2 may have positive debt.

## Proof

Condition before any whole date. Positive Never masses ensure positive
survival. Pulling back every suffix finite/Never response proves that
ALL-END holds in this conditional tail. Fubini and zero observer debt
prove that every positive observer atom is a full-cap response there.

After the last finite atom of every finitely supported owner, let S be the
remaining infinite-owner set. At a date in this tail let f_j be total
remaining finite probability and a_j the current atom, in the mass-one
conditional law. Then `0<=a_j<=f_j`, both are zero outside S, and
`beta=sum_j f_j` tends to zero at later dates. Let E_i be the Never payoff
minus the immediate-Quit payoff. Uniformly over the date,

    E_i=sum_j Gamma_ij f_j-sum_j J_ij a_j+O(beta^2).

The error consists only of outcomes involving at least two opponents'
finite clocks or two simultaneous opponent atoms. Bounded rewards and
independence give a fixed O(beta^2) bound. ALL-END gives E_i>=0; a_i>0
for i in {0,1,3} gives E_i=0.

If(1) holds and the atoms indexed by A vanish, then

    sum_i l_i E_i <=-eta beta+O(beta^2)<0             (2)

at every sufficiently late nonempty tail, for one eta>0. This follows by
maximizing each `d_j a_j` on `[0,f_j]`; no lower bound on an individual
mass is needed.

On S=013, at an observer0 atom the first certificate's left side is
`E1+(19/20)E3>=0`, contradicting(2). On S=023, at an observer3 atom the
second left side is `(1/2)E2>=0`. On S=123, at an observer1 atom the third
left side is `(1/2)E3>=0`. Thus those three owner sets are impossible.

On S=012 choose a sufficiently late observer0 atom. If a1=0, the fourth
certificate gives `E0+(1/2)E1=(1/2)E1>=0`, contradicting(2). Hence a1>0
and E1=0. The fifth certificate now gives
`gamma E0+(1+epsilon)E1+E3=E3>=0`, another contradiction.

The same certificates apply after deleting coordinates with zero f and a.
They eliminate every proper nonempty owner subset containing an observer:

| Remaining owners | Certificate and contact owner |
|---|---|
|0, 01, 03|013 certificate, observer0|
|1, 12, 13|123 certificate, observer1|
|3, 23|023 certificate, observer3|
|02|first012 certificate with a1=0, observer0|

The singleton pivot set2 fails ALL-END directly:
`E0=Gamma_02 f2-J_02 a2<0`. This exhausts all fourteen proper nonempty
subsets. Each named owner has arbitrarily late atoms by its definition,
so the local contradictions exclude the asserted infinite supports.

## The entire benchmark ray M>11 lies inside the open chamber

Use the explicit Gamma and J of the
[no-child benchmark](CODEX_COORDINATOR__NO_CHILD_FIN4_BENCHMARK.md), with
premium `t=M-1>10`. Choose

    epsilon=min(1/20,(t-10)/20), gamma=t/5-epsilon.

For013 the effective coefficients `c_j+max(d_j,0)` are
`(-1/20,-1/20,-3/10)` in order0,1,3: the only positive atom coefficient
is d3=1/2, already included. For023 they are `(-1/2,-1,-1/2)` in order
0,2,3, and for123 they are `(-1/2,-1/2,-1)` in order1,2,3.
For the first012 certificate with a1=0 they are `(-1/2,-1,-1/2)`.

For the last012 certificate the finite-mass coefficients are

    (-epsilon, -1-gamma, 2epsilon-(t-10)/5),

all strictly negative. Its atom coefficients are

    (5-(1+epsilon)t, -5epsilon,
                       10+5epsilon-t^2/5+epsilon t),

also strictly negative. For the last coefficient, epsilon<=1/20 gives
the upper bound `10+1/4+t/20-t^2/5`, decreasing for t>10 and already
negative at t=10. Finally `Gamma_02=-1<0<t=J_02`.

Hence each fixed benchmark table with M>11 has an explicitly specified
open neighborhood in its twenty-four singleton/participant-pair entries
where the theorem holds. The finite remainder rewards affect only how
late(2) applies, not these raw conditions. This includes generic tables
without invoking a transfer of an old selected minimum to new rewards.

This support theorem leaves finite calendars and inherited endpoints. At
the exact M14 benchmark, the separate
[finite-mode exclusion](../exports/NO_FINITE_ACTUAL_MINIMA_AT_SMALL_PENALTY_M14.md)
removes finite actual source minima at sufficiently small selectable
penalties. That conclusion is not asserted throughout this open raw region.
Exact four-owner ALL-END tails exist in the benchmark, so the support
restriction itself does not exclude I4.

## Exact boundary control

The sign chamber cannot be omitted. Change only Gamma_02 in the M14
benchmark from -1 to +1. Let only owner2 have finite mass f in (0,1),
with atoms `f z(1-z)^n`, n>=0, and put its remaining mass at Never;
all other players always choose Never. Choose z=1/26. The active owner's
payoff and cap are zero. Each observer's Never payoff is f, and its
date-n payoff is

    f[1+(1-z)^n(z J_i2-1)].

Here J_02=13 and J_12=J_32=-5, so every finite payoff is at most f.
Thus this actual profile is ALL-END with zero debts for all players,
positive Never masses, and only one infinite owner. It fails the strict
Gamma_02<0 guard. This is a full-response control, not a bounded-calendar
test or a positive-gap example.

## Actual-source adapter and precise narrowing

Consider the actual branch of a native zero-observer-debt source at pivot2:
an actual law profile with positive marginal Never masses, zero debts on
0,1,3, and full caps attained by Never. No minimum property is used by
the theorem, so it applies in particular when that branch is selected by
minimizing `d2+rho product_i N_i` on the zero-observer-debt carrier.
Read Gamma and J directly from the unchanged native reward table, verify
the five finite coefficient tests and the one singleton-pair sign, and
apply the theorem to that actual profile. Every one-, two-, or three-owner
infinite-support alternative is thereby excluded. The only actual support
cases remaining are finite support and four infinite owners.

This consumer does not assert that every global minimizing semantic point
is actual, and it makes no assertion about an inherited endpoint executed
after an infinite head. The full actual-versus-inherited source reduction
is not proved here. Conditional on its actual branch, every hypothesis
used in this packet is exactly a listed property of that branch; no
calendar, convergence rate, continuation strategy, or positive gap is an
additional assumed strategic witness.

The improvement is stronger than a table-specific generic exclusion:
it gives a finite open raw condition in twenty-four entries, allows every
remaining reward to be arbitrary finite, and removes all proper nonempty
infinite-owner sets even without dispersion or genericity. It does not
show that a raw game satisfying these tests already has UE.

## Source correspondence and formalization shape

The complete-law interpretation used above matches
`quittingStoppingLawExpectedPayoff` and
`quittingStoppingLawReplacementPayoffCap` in
`UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`.
The two directions of strategic correspondence are supplied there by
`quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff`
and
`quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue`.
For an independently supplied law profile, the canonical realization is
identified by `quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff`
and
`quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`.
Thus the cap in this proof prices every unilateral behavioral deviation;
there is no restriction to Markov or bounded-memory replacements.

`quittingTerminalSemanticPair` and `quittingTerminalSemanticDebt` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean` supply the
prescribed/full-cap pair and its debt coordinates. Those declarations
were inspected under their stated imports. No Lean or Lake check was run
for this ordinary-mathematical argument, and the new support theorem is
not represented as already formalized.

A formalization should first prove the fixed finite raw certificate lemma:
given the five tests, exact ALL-END and observer-contact equations with
uniform quadratic errors imply that no proper remaining owner support has
arbitrarily late contacts. A second lemma derives those errors and contacts
from actual independent stopping laws and positive Never masses. The
combined theorem quantifies over every such actual profile and concludes
that its infinite finite-date support set is empty or all of Fin4. The
finite inequalities are hypotheses on raw reward entries, not a structure
field asserting the desired support conclusion or supplying a strategy.

Independent full review: [raw tail certificate](../feedback/FOUR_OWNER_TAIL_REGION__BY_ADVERSARY.md).
