# `W x C`: periodic evaluation and exact-chain capacity meet only at an attachment seam

## Classification

**Interface-disconnected.**  The periodic evaluator in `W` acts on an actual
infinitely repeated behavioral word.  The universal capacity in `C` acts only
on finite paths in the exact punishment-floor Nash--Bellman root
correspondence.  Repeating a product-action word does not repeat an exact
outward cap path unless an exact endpoint return or a co-realizing suffix is
also supplied.

This remains true even after strengthening the shared interface well beyond a
common reward table.  The rational four-player regression below uses:

* the same product actions for every canonical periodic window and every cap
  edge;
* exact Nash--Bellman transport between punishment-rational cap endpoints;
* one common stabilized player and phase branch with exploitability `1`; and
* a limiting exact all-Continue zero-charge cap.

Nevertheless, the realized periodic continuation is not the cap continuation
at which the action is exact.  `W` supplies no exact return connector between
the cap endpoints, so it supplies no path to which the universal quantifier in
`C` can be applied repeatedly.

This is not a `Consistent` witness for the full clusters.  The displayed table
fails universal `C` by the new singleton-lock screen: a separate
punishment-rational charge-one self-loop can be repeated forever.  The report
therefore distinguishes an exact compatibility regression for all exposed
window/cap equations from a certification of universal finite capacity.

The executable exact checks are in
`pair_w_c_attachment_seam_probe.py`.

## 1. One common rational table

Let

```text
I = {o,a,b,c}.
```

For every nonempty terminal coalition `S`, define

```text
r_o(S) = 1 if o is in S, and 0 otherwise,
r_a(S) = r_b(S) = 0,
r_c(S) = -3 if S={c}, and 0 otherwise.                 (1)
```

This specifies all `15` nonempty coalitions and has sharp reward bound `M=3`.
The behavioral punishment vector is exactly

```text
chi = (1,0,0,0).                                       (2)
```

Player `o` guarantees `1` by quitting immediately, and all-Continue opponents
hold its best reply to `1`.  Players `a,b` always receive zero.  Player `c`
guarantees zero by Never, while all-Continue opponents make Never optimal over
the solo payoff `-3`.  These lower and upper strategies compute (2) against
arbitrary behavioral profiles, not merely stationary profiles.

At date `t>=0`, let only `a` have positive Quit probability:

```text
p_t = 1/(t+2)^2,
A_t = (0,p_t,0,0).                                     (3)
```

Define cap annotations

```text
w_t = (3(t+1)/(t+2),0,0,0).                            (4)
```

Every datum is rational at every finite date.

## 2. The exact cap-facing equations

Write `s_t=1-p_t`.  Since

```text
s_t = (t+1)(t+3)/(t+2)^2,
```

one has the exact Bellman identity

```text
w_t = F(A_t,w_(t+1)).                                  (5)
```

The action is exact one-stage Nash at continuation `w_(t+1)`.  Player `o`'s
Quit endpoint is `1`, while Continue gives `w_t(o)>=3/2`.  Player `a` mixes
between two zero endpoints, player `b` is indifferent at zero, and player `c`
strictly prefers Continue to the negative solo possibility.  Thus (5) is an
exact Nash--Bellman edge, not merely an affine payoff identity.

Every `w_t` lies in `[-3,3]^4` and dominates (2).  Moreover,

```text
w_t -> w_infty=(3,0,0,0),                              (6)
```

and all-Continue is an exact zero-charge self-loop at `w_infty`.

The selected cap edges even have a bounded local potential.  Directly,

```text
w_(t+1)(o)-w_t(o) = 3/((t+2)(t+3)) >= p_t.             (7)
```

Consequently every finite selected cap path has charge at most `3/2`.  This is
only a bound on the selected edges.  Neither (6) nor (7) says anything about
the other exact roots of the table, so neither certifies universal `C`.

## 3. Exact canonical windows and the fixed `W` branch

For every `n>=0`, take the required inclusive canonical word

```text
W_n = (A_n,A_(n+1),...,A_(2n)).                         (8)
```

One-pass survival telescopes exactly:

```text
1-m_n = product_(t=n)^(2n) (1-p_t)
      = (2n+3)/(2n+4),
m_n   = 1/(2n+4) > 0.                                  (9)
```

Periodic repetition therefore absorbs almost surely.  Only `a` can absorb,
and every coordinate of `r({a})` is zero, so the honest periodic delivery is
exactly zero.

For player `o`, refusal/Never is worth zero and stopping at phase zero is
worth exactly `1`.  A later stopping phase is worth the probability of
surviving to that phase and hence is at most `1`.  No terminal reward for `o`
exceeds `1`; the other players have no positive deviation from their zero
delivery.  By the pure-stopping-time reduction,

```text
E(W_n repeated forever) = 1                            (10)
```

for every `n`.  Thus one may take `eta=1/2`, all natural numbers as the
selected windows, `o` as the stabilized player, and the finite phase-zero
branch as the stabilized branch.  This checks arbitrary unilateral behavioral
deviations through the exact finite stopping-phase/refusal taxonomy.

## 4. What is shared, and what is not

The same word in (8) is a genuine exact cap path.  In outward-chain order it
starts at `w_(2n+1)`, prepends

```text
A_(2n), A_(2n-1), ..., A_n,
```

and ends at `w_n`.  Its additive `C`-charge is

```text
Q_n = sum_(t=n)^(2n) p_t > 0,                           (11)
```

and (7) gives

```text
Q_n <= w_(2n+1)(o)-w_n(o).                              (12)
```

The corresponding one-pass Bellman telescoping identity is also exact.  With
periodically restarted delivery `nu_n=0`, it reads

```text
nu_n-w_n
  = ((1-m_n)/m_n) (w_n-w_(2n+1)).                       (13)
```

In particular, the cap endpoints do not close: the normalized owner drift is

```text
((1-m_n)/m_n) (w_(2n+1)(o)-w_n(o)) = w_n(o) -> 3.       (14)
```

This is already an exact shared interface between the window actions and cap
geometry.  It still does not put the infinite periodic profile into `C`'s
domain.

The reason can be seen at a single phase.  At the cap continuation
`w_(t+1)`, the owner obtains `w_t(o)>1` by Continue, so `A_t` is exact.  At
the realized periodic continuation `0`, the same player obtains

```text
Quit endpoint = 1,
Continue endpoint = 0.                                  (15)
```

Thus the same action is not exact Nash at the periodic continuation.  The
gap in (15) is precisely the fixed `W` phase obstruction.  Substituting the
actual periodic payoff for the cap annotation destroys the exact-root premise
of `C`; substituting the cap annotation for the actual payoff destroys the
meaning of the periodic evaluator.

So the exposed equations separate cleanly:

```text
W: actual repeated-word payoff and complete stopping/refusal envelope;
C: exact annotated root edges and additive charge along finite paths.
```

They share a reward table and can share every one-pass action, but neither
cluster identifies actual periodic phase values with exact cap annotations.

## 5. The exact missing attachment datum

Let `u -> v` denote one outward exact punishment-floor path segment, with
nonnegative additive charge.  The selected window supplies

```text
w_(2n+1) -> w_n                                           (16)
```

with positive charge `Q_n`.  To turn periodic replay into repeated exact-chain
charge one needs an additional connector

```text
Gamma_n : w_n -> w_(2n+1),                               (17)
```

all of whose states remain in the reward box and whose first state is
punishment-rational.  Concatenating (16) and (17) gives an exact cycle with
charge at least `Q_n>0`; repeating it violates universal `C` immediately.
Therefore a table satisfying `C` must exclude every such connector.

Nothing in `W` asserts (17).  A behavioral word may be repeated because play
has returned to the unique nonabsorbed public history; an annotated
Nash--Bellman path may be repeated only if its continuation endpoint returns
exactly.  These are different notions of restart.

An equivalent missing datum is a suffix that simultaneously realizes the
endpoint cap as its payoff and as the complete envelope of unilateral
deviations.  Such a co-realizing suffix would justify replacing an annotation
by an actual continuation at the seam.  `W` gives actual evaluators but no cap
realization; `C` gives cap paths and a budget-to-go potential but no actual
profile realizing a cap.

This yields the smallest meaningful ternary seam:

```text
T supplies one exact cap-bearing tail and its endpoint provenance;
W supplies the stabilized evaluator branch for canonical windows of that tail;
C supplies the universal bounded budget on every exact punishment-floor path;
attachment asks whether the T/W branch forces an exact return connector or a
co-realizing endpoint suffix, contradicting C.                       (R_TWC)
```

Without `T`'s common prefix/endpoints and cap provenance, there is no canonical
choice of the two states in (17).  Without a proof of (17), periodic repetition
is not an exact-chain cycle.  This is why the useful next problem is the
`T x W x C` attachment seam rather than another pairwise inequality.

## 6. Singleton-lock screen: why this is not full `C`

The exact local cap regression above must not be mistaken for universal
capacity.  Set

```text
u = r({o}) = (1,0,0,0).                                  (18)
```

For every outsider `j`, table (1) gives

```text
r_j({o,j}) = r_j({o}) = 0.                               (19)
```

The singleton-lock lemma therefore applies.  At continuation `u`, the pure
root in which only `o` Quits is exact Nash, has successor `u`, and has charge
one.  The state is punishment-rational by (2).  Repeating the root gives
exact chains of charge `N` for arbitrary `N`.

Hence the table has

```text
local cap self-loop:       exact, charge zero;
selected window cap paths: exact, uniformly bounded total charge;
universal C:               false, by a different charge-one self-loop. (20)
```

This is the required negative control against certifying `C` from one harmless
cap.  Any future full `W x C` model with a positive-solo window witness must at
least satisfy the singleton-lock screen

```text
for every relevant positive-solo owner o,
exists j != o with r_j({o,j}) > r_j({o}).                 (21)
```

Passing (21) is necessary, not sufficient: mixed positive-charge cycles and
arbitrarily long nonrecurrent exact paths must also be excluded by one global
capacity proof.

## 7. The strict-joiner singleton-blocker candidate

An earlier research note proposes a different rational four-player table
which deliberately passes the singleton-lock screen (21).  For an owner `o`
quitting at rate `p` and a designated outsider `j`, its exact rate-covering
gain has the affine form

```text
g_(j,o)(p)
 = p [r_j({o,j})-r_j({o})]
   +(1-p)[r_j({j})-r_j({o})].                            (22)
```

Thus `j` strictly blocks that owner at every `p in [0,1]` exactly when both
endpoint gains are positive.  The candidate uses blockers

```text
o -> j : 0->2, 1->0, 2->3, 3->1.
```

For each pair the join endpoint in (22) is `1/4`, while the solo endpoint is
also strictly positive.  This is an exact useful improvement over the local
table above: it eliminates the singleton-lock self-loop at every owner rate,
not only at a finite rate grid.

The independent probe
`pair_w_c_blocker_candidate_screen.py` reconstructs all `15` coalitions and
checks the four affine certificates.  It also checks that none of the `15`
pure nonempty quitting-coalition fixed points is exact Nash.  Since all
rewards are nonnegative, Never guarantees every player at least zero.  If all
three opponents Quit surely at date zero, Continue pays `1/8` and joining pays
zero, so the behavioral punishment values satisfy the certified enclosure

```text
0 <= chi_i <= 1/8.                                      (23)
```

This does not compute `chi` exactly.

The reported search over `76,917` roots/words is not reproduced here and is
not evidence for universal `C`.  More importantly, an exploitability or
finite-word search is not automatically a search in the exact outward
Nash--Bellman relation.  The candidate does not specify a canonical common
`W` tail, cap endpoints, or optimized provenance, so it does not alter the
pair classification.

The exact one-sided charge-cycle search it should face is the following.  For
each period `L` and each support mode (`0`, interior, or `1`) of every player
at every phase, solve over real algebraic data

```text
v^(k+1) = F(a^k,v^k),              k mod L,
v^k in [-2,2]^4,
a^k in [0,1]^4,
a^k is exact one-stage Nash at v^k,
v^0 >= chi,
sum_k [1-product_i(1-a_i^k)] > 0.                         (24)
```

Writing `G_i^k=Quit_i(a^k_-i)-Continue_i(a^k_-i,v^k)`, the
support-free complementarity inequalities are exactly

```text
a_i^k G_i^k >= 0,
(1-a_i^k) G_i^k <= 0.                                   (25)
```

Equations (24)--(25), not a rate grid, include irrational mixed roots.  Until
`chi` is known, imposing `v^0_i>=1/8` gives a certified sufficient search
region by (23): any positive-charge cycle found there is punishment-rational
and kills `C` immediately.  Exhaustive exclusion requires the exact floor.
The first unresolved cells are period-one three- and four-mixer supports,
then off-grid mixed supports at periods two and three; the rate cover only
forces a singleton support to expand and does not exclude those cells.

Failure to find a cycle through any bounded period cannot prove `C`:
arbitrarily long nonrecurrent exact paths must still be bounded by a global
budget-to-go potential.  The candidate is therefore a worthwhile input to a
one-sided exact cycle refuter, not a capacity witness.

## 8. Precise residual and scope

There is no full `W x C` inconsistency or consistency claim here.  The pair is
interface-disconnected at the decisive quantifier boundary.  A direct full
consistency construction would still have to produce one rational table such
that:

1. its canonical compatible windows have a common positive exploitability
   margin and a stabilized player/branch;
2. its complete behavioral punishment vector is computed;
3. its augmented caps remain boxed and punishment-rational and converge to an
   exact zero-charge all-Continue loop;
4. every exact punishment-floor chain, including all off-cap pure and mixed
   roots, has one common finite charge bound; and
5. any claimed common origin of the windows and caps carries exact prefix,
   endpoint, and optimized-selection provenance.

The regression establishes items 1 and 3, plus exact cap transport stronger
than item 3.  It fails item 4 by (18)--(20) and makes no optimized-minimizer
claim in item 5.  The full capacity/provenance residual is not hidden behind
the local equations.

Run:

```text
python Experiments/counterexample_pairwise_consistency/pair_w_c_attachment_seam_probe.py
python Experiments/counterexample_pairwise_consistency/pair_w_c_blocker_candidate_screen.py
```

The attachment probe uses `fractions.Fraction` only.  It checks all `15` terminal
coalitions, the exact punishment-floor strategies encoded by the table, `256`
cap edges, `96` canonical windows, exact pass survival and normalized drift,
the fixed periodic phase witness, the mismatch (15), the limiting cap, and
the singleton-lock self-loop.  The arbitrary-window and arbitrary-chain
conclusions are the symbolic arguments above, not inferences from a finite
search or floating-point tolerance.

The candidate screen is also exact rational arithmetic.  It certifies only
the affine rate covers, absence of pure charged fixed roots, and (23); its
output explicitly leaves mixed charge cycles, universal capacity, and a
canonical `W` family unchecked.

The construction already uses four players.  It does not establish
cardinal-minimality and does not survive passive player extension as a full
`C` candidate, because its charged singleton loop already persists.  It is
only an exact interface regression and a formulation of `(R_TWC)`.
