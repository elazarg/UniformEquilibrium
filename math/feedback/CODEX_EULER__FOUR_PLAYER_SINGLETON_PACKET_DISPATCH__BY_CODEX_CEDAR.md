# Review of `CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH`

Reviewer: `CODEX_CEDAR`

## Scope checked

I independently checked the current Sections 2--9, with particular attention
to:

- purification of the owner rate to `p=0` or `p=1` off the two owner equality
  faces;
- the affine endpoint and cross-product criterion on an equality face;
- the generic three-defect dispatch `(J_b,J_a,J_ab)` and the packet-interface
  boundary family;
- promotion of a positive join defect to a sure-exit candidate or an explicit
  strict membership toggle; and
- Proposition 9.1's finite-cycle conclusion and its stated noncompiler scope.

I compared the formulas with the ordinary mathematical content of
`QuittingCollisionOwnerOptimal`, `QuittingCollisionSpectatorNoJoin`,
`QuittingCollisionBlockerBalance`, and `quittingCollisionRepairWorks_iff` in
`UniformEquilibrium/Quitting/Boundary/Repair/CollisionRepairCharacterization.lean`,
and with `isQuittingSureExitSet_iff_forall_max` and the pure-set unrestricted
terminal-Nash equivalence in
`UniformEquilibrium/Quitting/Paths/SureExitSet.lean`.

## Verdict

**VALID ordinary mathematics in the stated reduction scope.**  I found no
mathematical objection.

## Checks

### 1. Rate purification and the affine rows

The owner condition really is

```text
max(O0,O1) <= (1-p)O0+pO1.
```

Thus a strict positive endpoint difference forces `p=1`, a strict negative
difference forces `p=0`, and only equality permits an interior rate.  After
this reduction, the blocker row is exactly

```text
(1-p)(chi_y-r_y(y)) + p(r_x(y)-r_xy(y)) <= 0,
```

and the two spectator rows are the displayed affine join defects.  The packet
floor makes the blocker row automatic at `p=0`.

Lemma 4.1 is also exact.  A row with `u>0>=v` imposes
`p>=u/(u-v)` and one with `u<=0<v` imposes
`p<=-u/(v-u)`.  Cross multiplication of these positive-denominator bounds
gives precisely

```text
u_i v_j <= v_i u_j.
```

The zero-endpoint cases correctly force an endpoint and introduce no missing
case.

### 2. Generic sign dispatch

For orientation `(a,b)`, `alpha<0` forces the singleton endpoint and the only
remaining spectator obstruction is `J_b`; `alpha>0` forces the pair endpoint,
where blocker feasibility is `beta>=0` and spectator feasibility is
`J_ab<=0`.  The reversed orientation gives the symmetric statement.  Hence
the three implications in (5.4) are exactly the negations of the available
repairs in every nonzero sign chamber, including the two mixed-sign chambers.

The Section 7 family is a genuine packet-interface falsifier of any attempt
to infer those nonsingleton signs from packet axioms alone.  The singleton
mixture is zero coordinatewise, the positive masses pin the zero target, and
`chi_i<=max(r_i({i}),0)=0` makes the floor independent of the nonsingleton
completion.  The two selected spectator defects are identically one for all
rates.  The note correctly disclaims counterexample status because all-Never
is already an exact equilibrium.

### 3. Join promotion and finite toggle residual

Lemma 8.1 is the exact contrapositive use of the sure-exit characterization.
The newly joined player already satisfies its retention inequality strictly;
if no old member has a strict leave gain and no remaining outsider has a
strict join gain, every sure-exit inequality holds.  The concrete lists
(8.4)--(8.5) exhaust the old-member and remaining-outsider toggles in the two
coalition sizes.

Proposition 9.1 is valid, including the empty coalition.  If no sure exit set
is available, every vertex of the four-dimensional coalition cube has at
least one strict outgoing membership toggle.  Starting with the anchored join
and choosing one outgoing toggle at each subsequent vertex produces a repeat
within the finite 16-vertex cube; the segment between the first repeated
occurrence is a reachable simple directed cycle.  Bipartiteness makes its
length even, and a two-cycle is impossible because it would require the same
player's payoff comparison in both strict directions.  The possible lengths
are therefore exactly among `4,6,...,16`.

This finiteness does **not** make the cascade terminate at a sure exit set and
does not compile the repeated cycle.  It gives a finite path followed by a
finite strict-toggle cycle certificate.  Section 9 states this limitation
correctly: Bellman balance, hazards, and passive-player inequalities remain
additional data.

## Scope conclusion

The note supplies a clean finite, relabeling-invariant reduction of the
support-two collision screen and a finite strict-toggle residual under a
terminal witness.  It is neither a closure theorem nor evidence that an
arbitrary toggle cycle is implementable.  No export judgment was requested
or made.

## Follow-up review: Section 10 blocker-anchored four-cycle

I independently checked Proposition 10.1 and the residual disjunction
(10.9).  **Verdict: VALID ordinary mathematics.**

The arrows in

```text
{b}->{b,s}->{b,s,t}->{b,t}->{b}
```

give exactly the four signs in (10.2).  Player `s`'s action gap is
`(1-q)g_s^0+qg_s^1`, so its unique interior zero is
`q=g_s^0/(g_s^0-g_s^1)`.  Player `t`'s gap is
`(1-p)g_t^0+pg_t^1`, with unique interior zero
`p=-g_t^0/(g_t^1-g_t^0)`.  Thus the assignment of `p` to `s` and `q` to `t`
in the product root is correct, including the apparently crossed dependence;
all four strict signs put both probabilities in `(0,1)`.

The weights in (10.4) enumerate the four independent `(s,t)` outcomes when
`b` Quits surely.  Equation (10.5) is precisely the remaining spectator
`a`'s forced-Quit join value bounded by its prescribed Continue payoff.
When `b` deviates to Continue, the outcomes `{s}`, `{t}`, `{s,t}` contribute
the first three terms of (10.6), while the `(s,t)=(Continue,Continue)` event
of probability `(1-p)(1-q)` reaches `b`'s punishment continuation.  A row
whose cap is at most `chi_b+epsilon` therefore gives the displayed bound
`V_b+epsilon`.

Full behavioral coverage is sound.  Prescribed sure Quit by `b` makes every
deviation of `s`, `t`, or `a` terminate at date zero, so their arbitrary
behavior strategies reduce to the controlled initial binary action.  If `b`
Continues initially, only the joint-Continue mixer event reaches the chosen
stationary near-minmax punishment, whose unrestricted unilateral cap handles
all of `b`'s later behavior.  The first row under the prescribed profile
always absorbs and pays the same fixed vector `V`, independently of
punishment accuracy; hence the fixed-target terminal-selection waist applies.

Finally, under a terminal exploitability witness both weak inequalities
(10.5)--(10.6) cannot hold, because Proposition 10.1 would yield terminal
approximate equilibria at all positive tolerances.  Their exact negation is
the strict two-arm disjunction (10.9).  This compiles only this
blocker-anchored four-cycle shape and leaves its two explicit failure
chambers; it does not assert that arbitrary strict toggle cycles compile.

## Follow-up review: Propositions 10.2, 10.3, and 11.1

I independently checked the two remaining four-face compilers and the
nonempty-persistent-base extension.  **Verdict: all three are VALID ordinary
mathematics in their stated scopes.**

For Proposition 10.2, both fixed base members Quit surely, so the product
root on the two free coordinates is again the literal matching-pennies root.
Every free-player and outsider deviation is decided at the initial absorbing
row.  The only deviations that can remove absorption are the two base-member
leave deviations, and the two displayed average-payoff inequalities (10.10)
are exactly their unrestricted continuation comparisons.  No punishment
continuation is being smuggled into this case.

For Proposition 10.3, the strict signs give

```text
q=(A-B)/(A-C),        p=(E-D)/(F-D)
```

in `(0,1)`, with the apparently crossed assignment forced by which opponent
randomizes each active player's payoff gap.  Direct enumeration gives the
displayed absorption denominator and prescribed vector `U`, including
`U_s=B` and `U_t=E` from the two active Bellman equalities.  The passive
quantity `J_i` is exactly the forced-Quit payoff against the stationary root;
`J_i<=U_i` controls every pure stopping time because, after any all-Continue
history, the same stationary problem restarts.  Opponent deletion still has
positive absorption, so the endpoint compiler covers unrestricted behavioral
deviations.  The negations of the two passive inequalities are exactly the
two residual arms (10.19).  The proposition is a conditional compiler for
this empty-base square, not an existence assertion for arbitrary toggle
cycles.

For Proposition 11.1, fixing a nonempty persistent base `B` leaves a finite
binary game on the free face `F`; a mixed Nash equilibrium `mu` exists.  Its
best-response inequalities control all free-player initial actions.  When
`|B|>=2`, one base member's deviation still leaves another sure quitter, so
the displayed base-leave and outsider-join tests (11.4) exhaust arbitrary
deviations.  When `B={b}`, only the event where every free player Continues
can reach the accuracy-dependent near-minmax continuation for `b`; its weight
is exactly `mu(empty)`, giving (11.5).  Thus the all-behavior argument is
valid in both cases.

The residual quantifier is also correct: under a terminal witness, **every**
induced Nash equilibrium must violate at least one applicable outsider-join
or base-leave inequality, since any one equilibrium passing all tests would
compile.  This is a finite semialgebraic screen for cycles with nonempty
intersection.  Empty-intersection cycles remain outside Proposition 11.1,
and no claim is made that a general strict-toggle cycle is itself a Bellman
or chronological cycle.

### Addendum: Corollaries 11.2--11.3

Both corollaries are valid.  The induced finite-game Nash set is nonempty and
compact, and the maximum `G` of the finitely many continuous leave/join
excesses is continuous.  Proposition 11.1 plus the terminal witness gives
`G(x)>0` at every Nash equilibrium, so the attained minimum is strictly
positive.  This is only a face- and table-specific gap, exactly as stated.

For the cube count, a nonempty persistent base leaves at most three free
coordinates, so a simple cycle has at most eight vertices.  A six- or
eight-cycle necessarily uses all three free coordinates and hence has a
singleton persistent base.  Thus, after the four-cycle screen, only lengths
six and eight remain in the persistent-base residual.

## Follow-up review: Propositions 12.1--12.4

I independently checked the empty-base stationary screen, its negative and
positive exact tests, and the transverse open chamber.  **Verdict: all four
propositions are VALID ordinary mathematics in their stated scopes.**

For Proposition 12.1, `d_i` is exactly the probability that some other active
player Quits.  Hence `H_i=0` is equivalent to

```text
Q_i=N_i/d_i,
N_i+(1-d_i)Q_i=Q_i.
```

This is precisely active-player Quit/Continue indifference at the stationary
fixed point.  The common value equals the literal payoff `U_i` after dividing
the one-row absorption recursion by `delta>0`.  For a passive player, its
Continue endpoint is `U_o` and its forced-Quit endpoint is `J_o`.  At least
two strictly positive active rates give strict opponent contraction for every
active player, while total active absorption contracts every passive player;
therefore the stationary endpoint compiler covers all pure times, Never, and
arbitrary behavioral deviations.  Clearing the positive denominators gives
exactly a finite polynomial screen; no existence is inferred from cycle signs.

Proposition 12.2's arithmetic is exact.  The six displayed toggle margins are
respectively `1,1,1,2,1,1`.  For player 1, every nonempty opponent-only row
pays `2`, while forced Quit pays `1` only when both opponents Continue, so

```text
H_1=(x+y-xy)*((1-x)(1-y)-2)<0
```

throughout the open square.  Player 4 is neutral.  The table already has the
pure sure-exit singleton `{2}`, so this is only the claimed graph-sign versus
stationary-Bellman separation.

For Proposition 12.3, direct enumeration gives

```text
N_1=q_1 d_1+A_1(p_2-p_3),   Q_1=q_1,
H_1=-A_1(p_2-p_3),
```

and the cyclic analogues.  The six cycle margins have the stated order, and
the active equations force the three interior rates to be equal.  The active
stationary payoff is exactly `(q_1,q_2,q_3)`; the one remaining passive test
is sufficient, not automatic.

For Proposition 12.4, the general row indeed has

```text
H_i=a_i x(1-y)+b_i(1-x)y+c_i xy.
```

The chosen `c_i` makes the common rate `p_0` a zero.  At that point the two
partial derivatives are `-b_i` in the high-opponent variable and `-a_i` in
the low-opponent variable.  In cyclic variable order the determinant is

```text
product_i(-a_i)-product_i b_i,
```

so the stated nonzero condition supplies the ordinary parameterized IFT.
Interior rates, all six strict margins, and a strict passive inequality persist
after shrinking the full reward-table neighborhood.  For the rational test
`a_i=-1`, `b=(1,1,2)`, `p_0=1/2`, the determinant is `1-2=-1`, and the passive
zero-versus-minus-one comparison is strict.  The open chamber uses the extra
balanced/transversality data; it is not a consequence of strict toggle
recurrence alone.

### Addendum: Proposition 12.5

The support-incidence deduction is valid.  For positive support weights
`mu_i,mu_j`, pinning at `r_i(i)` and singleton-mixture feasibility imply

```text
mu_i r_i(i)+mu_j r_j(i)>=r_i(i),
```

so `r_j(i)>=r_i(i)`; the reverse inequality follows in the other supported
coordinate.  Among every unordered pair of the three cyclic active labels,
one label is the other's designated low opponent, where (12.18) gives the
strict opposite inequality `r_j(i)=q_i-b_i<q_i=r_i(i)`.  Thus at most one
active label can lie in the two-point packet support.  With three active and
one passive player, support size two then forces exactly one supported active
owner and the other supported owner passive.  This is only the stated label
restriction; it supplies none of the remaining packet, floor, or source
fields.

### Addendum: Proposition 12.6

The exact crossed-packet incidence witness is valid.  The half-mixture of
singleton columns `r_1,r_4` is `(0,0,1/2,0)>=0`, the supported owner
coordinates are pinned at zero, and every own singleton reward is zero.
Thus the completion-freedom bound places every punishment value at most the
zero target.  The two crossed chains are exactly

```text
r_1(2)=-1<r_2(2)=0<r_4(2)=1,
r_4(3)=-1<r_3(3)=0<r_1(3)=2,
```

so both owner screens use a preemption margin at least one.

The active singleton and pair entries agree with (12.18) for
`a=-2,b=1,c=1`, and the common active rate `1/2` gives payoff zero.  Under the
passive completion, six of the seven nonempty active coalitions pay player 4
one, giving `U_4=(6/8)/(7/8)=6/7`; forced Quit pays minus one on the seven
nonempty active outcomes and zero on the empty outcome, giving `J_4=-7/8`.
The stationary compiler therefore applies with fixed payoff
`(0,0,0,6/7)`.  Openness is correctly claimed only for the compiler/cycle
chamber, not for preservation of this exact packet mass and target.

## Follow-up review: Propositions 13.1--13.2

**Verdict: VALID ordinary mathematics.**

The eight arrows alternate the low-player join margin `b_i` and high-player
leave margin `-a_i`.  Marginalizing the neutral opponent contributes only the
baseline `q_i d_i`; hence the active polynomial is exactly

```text
H_i=a_i p_h(1-p_l)+b_i(1-p_h)p_l+c_i p_h p_l,
```

independent of the neutral rate.  The chosen `c_i` makes the common `p_0`
root exact.  At that root the high and low derivatives are `-b_i` and `-a_i`,
respectively, giving matrix (13.6).  Direct block determinant expansion gives

```text
(b_1 b_3-a_1 a_3)*(a_2 a_4-b_2 b_4).
```

Thus the two nonzero factors supply the stated parameterized IFT and an open
interior stationary compiler chamber.  With four active players there is no
passive inequality, and every player has strict opponent contraction.

For Proposition 13.2, `a=-2,b=1,p_0=1/2` gives `c=1` and determinant factors
`-3` and `3`.  The four singleton columns match the high/low/neutral
assignment exactly.  Their half-mixture on support `{1,3}` is
`(0,1/2,0,1/2)>=0`, both owners are pinned at zero, and zero own singleton
rewards give the required punishment floors.  The crossed chains in (13.10)
are exact with unit preemption margins.  Completing by (13.4), the common
half-rate profile has fixed payoff zero and satisfies the stationary
all-behavior compiler.  This is the claimed exact packet-level incidence,
not a general completeness result for empty-base cycles.

### Addendum: Corollary 13.3

The support-label classification is valid.  Every adjacent pair in the
four-cycle contains one ordered low relation, contradicting the mutual
off-diagonal inequalities forced by positive two-point packet masses and
pinning.  For the two opposite pairs `{1,3}` and `{2,4}`, each label is the
other's neutral opponent, so both cross singleton values equal the respective
own pinned values.  Thus the constant-containing eight-cycle family permits
only the two opposite support patterns; this is a label screen, not a claim
that either pattern automatically supplies all packet fields.

## Follow-up review: Propositions 14.1--14.3

**Verdict: VALID ordinary mathematics.**  I independently enumerated the
three-cube cases and recomputed every displayed sign and determinant.

For Proposition 14.1, a six-cycle uses three vertices in each bipartite
class, so the omitted vertices have opposite parity and Hamming distance one
or three.  An omitted edge has exactly the three layer types `01,12,23`; an
omitted antipodal pair has exactly the two cardinality types `03,12`.
Deleting a representative pair in each case leaves the unique displayed
Hamiltonian six-cycle, up to coordinate relabeling and dihedral symmetry.
Thus the five representatives are exhaustive and inequivalent under the
stated equivalence, without using cube complementation as an extra symmetry.

For Proposition 14.2, all fifteen row triples sum to zero.  Reading an add as
`delta_i(R)>0` and a removal as `delta_i(R)<0` verifies all six arrows in each
of the five representatives; the three cycles meeting `empty` use exactly
`q_1=1` on the empty join and `q_3=-1` on the empty leave.  At the common
half-rate, `H_i` is one quarter of the row sum.  The derivative rule

```text
(u,v,-u-v) -> (-v,-u)
```

gives determinants, in the displayed order,

```text
68, -32, 64, 63, -12.
```

The passive zero-versus-minus-one completion is strict.  Hence the ordinary
IFT gives the claimed full-dimensional local compiler chamber for each
shape; it does not make the stationary screen sign-forced.

Proposition 14.3 is also valid.  For one coordinate, toggle orientations
alternate.  If both orientations occur away from `empty`, their prescribed
positive and negative deltas can be balanced.  If only one occurs away from
`empty`, the opposite toggle is the unique empty edge, so that coordinate is
toggled exactly twice; because at least two opponent coordinates remain,
there is an unused nonempty context on which to place the balancing sign.
Thus the sign cone meets the zero-sum hyperplane in a nonempty relatively open
set.

On that hyperplane the map

```text
L(delta)_j=sum_(R containing j) delta(R)
```

is surjective: with `k=|F|-1`, the singleton/full-context construction
`y=sum g/(k-1)`, `delta({j})=g_j-y`, `delta(F\{i})=y` has zero total and image
`g`.  At the half-rate the gradient row is the positive scalar
`2^(2-k)L(delta)`.  The open mapping theorem therefore makes each allowable
Jacobian row range open; their product is an open subset of the zero-diagonal
matrix space.  Since determinant is not identically zero there (a cyclic
permutation matrix is one witness), this open set contains an invertible
Jacobian.  The IFT and strict passive completion then give exactly the claimed
availability result.  The proof selects reward magnitudes inside each sign
pattern and does not consume an arbitrary strict-cycle table.
