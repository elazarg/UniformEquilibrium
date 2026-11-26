# Independent review of exact Nash nonattainment

Reviewer: CODEX_LOCAL_COLLAR_REVIEW. Mathematical verdict: **PASS**.
No unresolved mathematical objection. Ordinary mathematics only; no Lean
command ran and no export approval is claimed.

Reviewed artifact:
`math/notes/CODEX_NEGATIVE_CAPS__EXACT_NASH_NONATTAINMENT.md`

SHA256:
`21398bb9acd2987538cfde743dbdd0969ab6929806a4baafa009746b0ccc5646`

The review was independent of the other review. It covers Sections1--6,
including the added semantic-closure corollary. The reviewer requested the
explicit definition of C as original payoff minus1; that clarification is
present in the pinned artifact.

## Exact claim and its limits

For all sufficiently small independently positive e,h1,h3, the complete
calibration has no exact terminal Nash profile under arbitrary independent
behavioral stopping laws, including infinite supports and positive Never
masses. The same parameter threshold makes every bounded continuation
sequence satisfying(2) nonnegative. Every zero-debt point in the semantic
closure of all actual shifted payoff/cap pairs is consequently nonnegative.

The result does not supply a positive exploitability gap, rule out
arbitrarily accurate equilibria, itself produce a uniform equilibrium, or
exclude partial-Nash global minima. Its intersection with existing UE
existence classes is consistent: exact attainment is a stronger demand.

## 1. Source semantics and the two finite inputs

C_i^t is explicitly the original conditional terminal payoff minus1.
The AllNever contribution to this annotation is therefore-1, while the
original game's literal Never reward remains zero. This distinction is
essential to the final consumer and is correctly maintained.

The actual continuation bounds[-3,10], C2<=2 follow from the complete
reward table and this Never contribution. The sure-owner census in
Section8 of the unequal-premium export has an explicit box containing a
common neighborhood of zero in all three positive parameters. Its only
continuation bound is coordinate2>=-3; it therefore also applies to the
abstract child cap used in Section6.

After sure hazards are excluded, every finite joint reach is positive.
Replicating a profile through such a date and replacing the subsequent
strategy multiplies any tail improvement by that positive reach. Thus
every actual tail is exact Nash. Its positive Continue probability gives
the first equality in(2), and its positive Quit probability gives the
active equality. No subgame-perfection premise is being imported.

I independently checked the zero-premium certificate used in(3).
Q^0=Gamma*q+H*C with C>=0,C2<=2 gives exactly the four inequalities
printed in the artifact, including their closed-cube boundary cases.
The two-variable Bernstein certificate in the cited cap-region note
recomputes to minimum coefficients

    313/144, 5/9, 2, 55/36

on the four half-squares, proving the required strict contradiction in
its nonzero branch. This check used exact symbolic rational arithmetic.

## 2. Proper negative supports and propagation

At zero premiums, a negative coordinate1 forces x,z,w>0, and a negative
coordinate3 forces x,y,z>0. Coordinates0 and2 are already nonnegative.
Thus012,023 and full support exhaust all possibilities.

For012, its active rows yield z>=3y>=3x and force the next coordinates1
and3 negative. All unit hazards in this proper support contradict an
active equality. The next phase is full, so its coordinate2 is zero;
the current row2 then gives x=y=s. Substituting the next full output gives

    5s=2HZW(X-5Y)>0.

The next row2 implies W>=2(X-Y)>8X/5, while the purported negative
coordinate equals H*Y*Z*[10W-(1-s)X]>0. All signs are strict as required.

For023, the active rows give z>=3w>=6x, and force the next coordinates1
and3 negative. Again all unit boundaries are excluded. The next full
coordinate2 vanishes, giving w=2x=2s and s<1/6. The two active equalities
give X>10(H0/H3)W>8W; the next row2 gives Y>15X/16. The expression

    C1^t=2s+2H0ZW[5Y-(1-s)X]

is then positive, a contradiction.

Every remaining negative phase is full. A nonnegative next vector would
contradict(3), so negativity propagates through an infinite full-support
chain. This is the place where the whole infinite sequence improves upon
a one-step invariant-region statement.

## 3. The full-chain exclusion

Coordinate2 is zero at every full phase, forcing w=2(x-y), so
a=y/x lies strictly between0 and1. The identities(4) follow directly
from rows1 and0 with K=2xzw and C0=5aK. Their second equation gives
B<=10a, hence A<=-2+7a.

I checked the discriminant calculation and algebra:

    B-5aA=30a^2-23a+6+(5a-1)b,
    min_a(30a^2-23a+6)=191/120.

For a<=1/4, A<=-1/4 excludes H1=0. For a>1/4, H1=0 would make
the same two identities force B-5aA<=0. Thus H1>0, H0>0, and every
hazard in the chain is strictly below1 even though the initial compact
limit allowed unit hazards.

The denominator t-A is strictly positive because H1*K'=x(t-A)>0.
Elimination of K' yields(6). For a>1/4, the displayed bounds give

    D/[5(t-A)] >= (191/120+b/4)/[5(4+b)] > 1/20.

The bracket in(6) is positive since a'>0, so multiplication by
H1/H0<1 yields the claimed decrease a'<a-1/20. Once a<=1/4, the
interval remains invariant: on[1/5,1/4] the same D is positive, and
below1/5 the alternative algebraic identity gives a'<1/5.

Finally A<=-1/4 gives K'>=K+x/4>=9K/8. This contradicts boundedness
of a positive K along an infinite chain. The proof does not assume that
a or K is bounded away from zero before entering that regime.

## 4. Compactness and the cubic bootstrap

The uniform small-premium extension is valid. If negative coordinates
were bounded away from zero, shift to such a date and extract a diagonal
subsequence of all subsequent bounded hazards and annotations. Relation(2)
is closed: its active assertion can be written q_i*(C_i-Q_i)=0. The
limit therefore satisfies precisely the zero-premium relation already
excluded, including possible unit hazards.

If a negative phase retained positive total hazard in the limit, its fixed
support can only be012,023,013 or full. Support013 is impossible before
taking limits by its active row0. The remaining three limiting support
arguments in the artifact all force q=0, now using the uniform lower
bound on continuation coordinates tending to zero. Thus the second
uniform smallness statement is justified independently of premium ratios.

For the quantitative bootstrap, I recomputed the constants:

- Full support gives s<9*delta from the sharper coefficient
  s<=(720/83)*delta when s<=1/2.
- For012, the printed component bounds give
  s<=(10210/4959)*delta<3*delta.
- For023, they give s<=(461/85)*delta<6*delta.
- Every negative coordinate is bounded below by -s^3/9, so the common
  s<=12*delta yields delta<=192*delta^3.

The supremum defining delta need not be attained; the bound holds at
every negative phase and passes to that supremum. With delta<1/20 the
last inequality forces delta=0. Compactness supplies one threshold
uniform over all independent positive premium ratios.

## 5. Actual exact Nash nonattainment

The reviewed cap-region activity theorem now applies at every actual
tail. Player0 can be active only alone; consequently all negative grand
terms disappear from the other players' Quit endpoints. Every player has
a strictly positive Quit endpoint whenever any opponent is active.

A solo-j phase forces its coordinate to zero now and at the next date.
Until the first other-owner activity this zero is preserved; that first
activity contradicts the strictly positive Quit endpoint. If no other
owner ever acts, an outsider in a negative singleton column instead has
an actual shifted payoff which mixes two strictly negative numbers:
Gamma_ij and the Never value-1. This is where actual realization, rather
than merely a bounded abstract continuation sequence, is used.

With solo phases excluded, player0 never acts. Row2's Continue identity
makes v_t=C2^t nondecreasing. At every positive z_t, its active equality
has v_t=e*D_t>0 and gives v_(t+1)>=v_t/e. Boundedness and e<1 therefore
allow only finitely many such dates. After the last one, player2's actual
shifted payoff is at most-1, whether players1,3 ever quit or not. This
contradicts nonnegativity and completes the unrestricted exact-Nash result.

## 6. The additional semantic-closure corollary

Compactness extracts a root and child pair from every semantic closure
point. The exact debt decomposition is R_i+h*d'_i, with both terms
nonnegative. Zero initial debt therefore makes the root full Nash against
the CHILD CAP vector, even before child debt is known to vanish.

The actual cap bound B'_2>=-e passes to the closure and is stronger than
the lower bound needed by the sure-root census. Thus the root is nonsure,
h>0, and child debt is zero. Repeating gives the bounded sequence(2), to
which the uniform nonnegativity theorem applies.

The artifact correctly refuses to apply Section5's actual Never-payoff
contradiction to this abstract sequence. It proves only nonnegativity of
zero-debt closure points, consistent with approximate equilibria and
possible nonattainment of their limiting targets.

The semantic endpoint declarations named in the artifact were inspected
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
No claim of new Lean implementation follows from this source inspection.
