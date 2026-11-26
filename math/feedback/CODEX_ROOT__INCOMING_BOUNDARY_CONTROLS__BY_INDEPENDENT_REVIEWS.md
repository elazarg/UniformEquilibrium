# Independent reviews of the incoming boundary controls

Both parts of [the canonical note](../notes/CODEX_ROOT__INCOMING_BOUNDARY_CONTROLS.md)
pass independent mathematical review for INTERNAL retention. They do not
pass the counterexample-coverage export gate: the displayed games have
absorbing equilibria and A=0. The first proof was reviewed at SHA256
`01fc321f22eeda2ea603e3548b3a7ab5536b8b57d419634bbdfc0e9effa8f833`;
the generalized second proof at
`5c347a9304ff3b14cc767067e2198ecf85e9eabd616127f86040f6ee4e692960`.
The canonical assembly normalizes headings, status and source locations and
includes an exact matrix-census reproduction. The mathematical claims and
proofs retain their reviewed scope. Review records below concern the
respective parts; supporting scratch-run descriptions are not dependencies.

# Independent review of the finite incoming-length obstruction

Reviewed artifact: `FINITE_INCOMING_LENGTH_OBSTRUCTION.md` in this directory.
Final SHA256:
`01fc321f22eeda2ea603e3548b3a7ab5536b8b57d419634bbdfc0e9effa8f833`.

Verdict: **PASS as a useful internal mathematical boundary. No export or
counterexample-class exclusion is approved.** The final scope correction
restricting the original absorbing example to R=Z+1 is necessary and valid.
I read the full proof, reconstructed its cap and ordering arguments, and ran
`FINITE_INCOMING_LENGTH_CHECK.py` successfully. No Lean command ran.

## Exact claim checked

One fixed table has det Gamma=32, R0 degree1, and a strict positive inverse
pivot column. For each n>=1 and every sufficiently small f>0, an actual
observer-optimal ALL-END tuple X_(f,n) has positive original Never, B1=f,
and the other three caps uniformly above1/8. Every finite incoming
factorization preserving the complete tuple and using any nonpivot activity
has at least n+1 dates, even when its continuation is an arbitrary compact-
carrier point. Every shorter factorization has total hazard below
-log(1-f). The original word attains the n+1 bound.

This refutes a fixed-length, uniformly active incoming rule throughout the
positive-premium collar under the listed carrier and singleton hypotheses.
It does not refute a rule using positive absorbing gap, actual global
minimality, further genericity, or the complete source restrictions.

## Table, actual profiles, and complete caps

The reward rules specify all coalitions, retain native own singleton zero,
and have absolute bound8. Recipients2 and3 are exactly insensitive to their
own coalition membership, so Q2=P2 and Q3=P3 at every product root.
The determinant, positive inverse column, all principal nonsingular minors,
and unique full-support LCP(-ones) solution agree with the exact checker.
Singleton-column negativity rules out homogeneous singleton supports; larger
homogeneous supports are impossible by principal nonsingularity. This proves
R0, and the unique offset root has positive index, giving degree1.

For the one-date Q_v tail I independently get
P=(5/16-19v/4,v,t,t+v) and Q=(0,0,t,t+v), with t=1/4.
Following AllNever gives the claimed prescribed values, full caps, and Never
offers. The head pivot masses sum to F=f(1-2^-n), and
F+(1-F)v=f. Each observer1 head deadline is exactly f; the joint-date
query is F; every later query and Never is f. For observers2 and3,
head queries are nonpositive and the displayed through-tail values are
positive. Pivot Never gives b_v, and early pivot Quit gives zero.
Thus the full augmented tuple (1), not only its prescribed payoff, is exact.
Every behavioral response is covered by the deadline/Never disintegration.

For 0<f<1/64 and n>=1, v<1/126. Consequently b_v>1/8;
B2>1/4-5/(4*64)>1/8 and B3>1/4-9/(4*64)>1/8. All original
Never coordinates are strictly positive and every observer has zero debt.

## Saturated defects and all incoming factorizations

With N1=1, independence gives exactly

    D2=2 Pr(T3<T0<infinity),
    D3=3 Pr(T2<T0<infinity).

This remains a nonnegative coordinate constraint on the compact carrier:
deleting player1's vanishing finite mass from approximants changes each
response payoff by a uniformly vanishing coupling bound. The displayed
root identities (3) follow either from these ordered-event probabilities
or directly from the exact root formulas; the checker verifies their
polynomials without a realization assumption on the tail.

In any incoming factorization of X, positive original Never makes every
root nonsure. N1=1 forces q1=0 throughout, and zero observer debt plus
ALL-END pass to every descendant. Before the first q2+q3>0 root, the word
is therefore pivot-only. With absolute pivot mass A already used, its
remaining cap and finite mass are exactly (4). The observer1 root comparison
2x<=B1 bounds each new absolute pivot atom by (f-A)/2, giving
A<=f(1-2^-L) after L dates, including any retained empty queries.

At the first nonpivot root, the saturated nonnegative defects force the
remaining tail's finite pivot mass to vanish. Since Q2=P2 and Q3=P3, an
active protected observer forces its tail cap to zero. With N0=N1=1 in
that tail, ALL-END gives B2=1-N3 and B3=1-N2. The original finite masses
of both protected players were positive and none was used earlier; hence
both must be active now and exhaust their masses, giving q2=t+v,q3=t.
This reasoning works on the augmented compact carrier by continuity.

The observer1 Never recursion is then x(1-t-v)(1-t)+(1-x)v, whereas its
retained source coordinates give x+(1-x)v. Their equality forces x=0.
All finite pivot mass F must thus have been spent strictly before that root.
The previous bound forces L>=n. The claimed n+1 lower bound therefore
quantifies over every product-root representation and every carrier tail,
not only alternative timings of the originally chosen profile.

If the word has at most n roots, it is pivot-only. Original Never gives
its survival at least1-F, and q<=-log(1-q) gives the displayed activity
bound. Choosing f<1-exp(-eta) defeats any proposed uniform activity eta
at any prescribed finite length m by taking n>=m.

## Limit and source-specific scope

At fixed f, the n-to-infinity tuple has the displayed exact coordinates.
The same defect and cap reasoning shows that any actual first nonpivot
date would require all pivot mass f to have been spent at finitely many
prior dates, impossible because f(1-2^-L)<f. Since both protected owners
have positive finite mass, such a first date would exist in every actual
realization. The limit is therefore nonrealized. Every finite incoming
factorization remains pivot-only. At f=0 the macroscopic Q0 root exists,
showing why an exact-face incoming theorem would not repair this collar.
No continuation is placed after an infinite calendar.

The positive-premium mechanism uses positive reciprocal protected
singletons. In Ratio these force G_j,G_k<0 while the target G_i>0.
Writing the observer block as -diag(G)c, a strict positive inverse pivot
column gives z=c^-1 1>0 and h dot z>0. Schur complementation yields

det Gamma=-(G_i G_j G_k)det(c)(h dot z)<0.

Thus this particular mechanism cannot also lie in the det-positive Ratio
source chamber. The proof does not assert that every possible positive-
premium length obstruction has this mechanism.

The literal table has sole sure quitter1 as an absorbing Nash profile,
so its native absorbing SUM-debt infimum is zero. R=Z+1 preserves that
example. Arbitrary negative shifts of the sole quitter do not: Never
would then yield zero instead of its negative singleton. The final draft
correctly fixes this scope point. No positive-gap minimum or no-UE example
has been constructed.

## Nonredundancy and retention recommendation

I compared the result with the old one-zero geometric-head compression,
the fixed-head moment-rigidity and small-new-head bounds, and the isolated
one-date observer-response-oval example. The old geometric obstruction
retains a chosen solo head and endpoint; the fixed-head results retain
particular endpoint constraints; the oval result concerns a fixed one-date
controller. None gives the present universal lower bound over arbitrary
finite incoming factorizations and arbitrary compact-carrier tails at an
actual tuple, nor the exact n+1 hierarchy at one fixed table.

Retaining this obstruction compactly in the canonical internal boundary
record is justified. It explains precisely why the newly proved uniform
incoming collar cannot be extended using these local carrier and matrix
conditions alone. It provides no new UE class and should not enter exports.
A globally selected positive-gap source, or different operations in the
remaining Ratio chamber, remains a distinct open target.

# Independent review of the two-zero no-incoming obstruction

Reviewer: FINAL_GLOBAL_REVIEW, 2026-11-09.

Reviewed artifact: `TWO_ZERO_NO_INCOMING.md` in this directory, SHA256
`5c347a9304ff3b14cc767067e2198ecf85e9eabd616127f86040f6ee4e692960`.

**Verdict: PASS as an internal full-carrier obstruction.** This is not an
export recommendation, a globally minimizing-source obstruction, or a
positive absorbing-gap example. The complete literal table has A=0 and an
explicit absorbing equilibrium. No Lean, Git, or tracked-file changes were
made by this review.

## Exact construction and full-cap limit

I independently checked the repeated-root formulas. A deadline at head date
t has value A_i(1-H_i^t)+H_i^t Q_i. This is monotone in t, regardless of
the signs of A_i and Q_i, so its maximum over the finite repeated block is
at one of the two endpoints. The remaining through-tail term prices the
entire continuation cap. Formula(1) is therefore an exact full-cap formula,
including unbounded behavioral replacements, rather than a finite list of
sampled deviations. Its denominators are positive for both rate vectors
used here.

The asymptotics in(2) follow by expanding the exact one-root probabilities:
P_i=(Gamma lambda)_i T/n+O(n^-2),
E_i=(Gamma lambda)_i T/n+O(n^-2),
1-H_i=L_i T/n+O(n^-2), and 1-c=Lambda T/n+O(n^-2).
All nonsingleton contributions are O(n^-2) per root because the table is
fixed and finite. The forced-Quit offer is O(n^-1). Thus the exact maximum
of three terms converges to the asserted full cap; no supremum-limit
interchange is assumed. The second block's tuple can depend on n: its
convergence and the bounded first-block coefficients are sufficient to
compose the limits. Every approximant uses exactly two finite n-stage
blocks followed by Never.

I verified independently that Gamma*(1,1,1,1)=(3,0,0,0) and
Gamma*(1,0,2,2)=(-4,2,0,0). For the second block, the pivot payoff is45/64
and its cap and Never offer are7/8; the other three coordinates vanish.
For the first block, the limiting passive ratios are(-1,2/5,0,0).
Its two pivot head-cap endpoints are0 and -(1-x^4); its through-tail cap
is (15/8)x^4-1>0 at x=9/10. The observer1 cap equals its prescribed payoff
(2/5)(1-x^5); both zero observers have all three cap terms tending to0.

Exact rational arithmetic reproduces the displayed U,B,e,N tuple, including

    d_0=4563431/32000000,
    nu=59049/1600000.

All original Never probabilities are positive and are exactly the displayed
values in every finite approximant. The higher rewards do not affect these
limits. Consequently the claim that the SAME X belongs to the carrier for
any fixed finite completion with the stated singleton matrix is valid; the
positive participant restrictions are used for the incoming obstruction.

## Obstruction with an arbitrary continuation

For the literal completion, I reconstructed the root polynomials and checked

    Q_2(q)=1-product_(a!=2)(1-q_a),
    Q_3(q)=1-product_(a!=3)(1-q_a).

Both are nonnegative on the full hazard cube, including sure components.
A semantic root's full cap is at least its forced-Quit offer, independently
of its continuation. The two zero cap coordinates of X therefore force all
four root hazards to be zero. For arbitrary strictly positive participant
entries, the same conclusion follows using their finite positive minimum.

The zero-root subtlety is handled correctly. A zero root preserves U,e,N
but maps B to max(0,B), so it need not be an identity at an arbitrary point.
Here e_after=e(X)>=0 and every carrier point satisfies B_after>=e_after.
The equality max(0,B_after)=B(X)=e(X) then forces B_after=B(X). Hence the
after-tuple is literally X. Induction proves that EVERY finite incoming
word with any carrier tail contains only zero roots and has tail X.

If X had an actual complete-law realization, its first root and then every
successive root would be zero by the same argument. Its original Never
vector would be(1,1,1,1), contrary to the displayed N. Thus the claim of
nonrealizability is proved, not inferred merely from the construction being
a diffuse limit.

## Source boundary and useful conclusion

The singleton matrix facts are correct: determinant6, strictly positive
inverse, R0 and degree1. In particular this obstruction is not explained
by a nonnegative singleton column or the earlier degree-zero pivot chamber.
The strict good-pair conditions J_20=J_30=1<Gamma_20=Gamma_30=2 also hold.
These facts nevertheless do not supply a globally selected source.

I checked the pure simultaneous23 profile directly. It gives native payoff
(0,0,1,1); either quitter would receive -1 by Continuing, while players0,1
receive0 whether they join or remain quiet. This prices every complete
response because an opponent quits surely at the first date. It is exact
absorbing Nash, so A=0 and min_C(d_0+r nu)=0 for every r>0. The displayed
X has strictly positive objective and cannot be a global minimum. The same
argument after adding1 to each nonempty-coalition recipient reward gives
original payoff(1,1,2,2); under every unilateral deviation an opponent still
absorbs immediately, so the shift is legitimate.

The valid no-go is therefore specific and useful: even at a strict-inverse,
degree-one singleton matrix, positive original Never, ALL-END, zero observer
debts, exactly two zero caps, positive remaining caps, and good pivot pair
premiums do not ensure ANY positive finite incoming word when the tail may
change arbitrarily. The one-zero theorem requires three positive cap
buffers; this example has only two, so there is no conflict with that
export. It decisively prevents extending that theorem using only the stated
local carrier conditions. A positive-gap/global-selection property, or an
operation beyond finite incoming words, would be an additional ingredient.

The example does not show that this X can arise as the endpoint selected
from a hypothetical positive-gap global minimum. It must remain internal
method guidance with this limitation explicit. Within that scope the proof
is complete and the claim passes independent review.


## Addendum: open raw criterion in the final Section5

**The generalized criterion also PASSES.** This binds the review to final
SHA256 `5c347a9304ff3b14cc767067e2198ecf85e9eabd616127f86040f6ee4e692960`.
I verified mechanically that deleting the new Section5 and restoring the
old section number reconstructs exactly the previously reviewed SHA
`ae2e24e8fb3368bc5d6060fcb355bb7d600e4d44c0d7e7478ba25043228e2909`.
There are no other changes to the earlier proof.

The computed rates w_i=-Gamma_jp/Gamma_ji and
w_j=-Gamma_ip/Gamma_ij are positive, and their cancellation of the two
observer drifts is an identity on the stated raw region. It does not impose
a fine-tuned reward equality. Every opponents' total rate is positive in
both blocks. The strict positive inverse column supplies an axis tail with
positive pivot payoff u and cap b and zero observer U,B,e.

For the first block, the formula for the pivot through-tail cap is the head
passive value plus exp(-L_p t)b. It strictly exceeds the last head deadline.
The other possible head-cap endpoint is zero; choosing t small enough that
e_p>0 deals with that endpoint even when g_p<0. Thus B_p=e_p for either
sign of g_p. Continuity from u,b>0 also gives U_p>0 for sufficiently small
t. The quiet fourth player has w_k=0 and g_k>0, so U_k=e_k=B_k>0. Both
zero observers have all three exact cap-formula terms tending to zero.
The same two-finite-block approximation therefore proves the full augmented
carrier statement, and the positive participant rows give the unchanged
no-incoming and nonrealizability conclusions.

Invertibility, the strict inverse-column signs, the four prescribed
singleton signs, g_k>0 and the finitely many participant signs are all open
conditions. The optional good-pair inequalities are also strict. The rates
and resulting coordinates vary continuously with the raw singleton entries.
At the literal witness, v=(1,1,1,1)/3, tau=3 log2 and
t=-log(9/10) reproduce the earlier tuple, with strict positive margins.
Those same durations consequently work nearby. The strict inverse, positive
determinant, negative columns/pair and negative outside triple rows persist
as stated. This establishes a nonempty open region of failure for the
proposed finite-incoming carrier lemma. It does not establish A>0, a global
minimizer in this geometry, or failure of UE anywhere in that region; the
literal A=0 example and the internal-only scope remain unchanged.
