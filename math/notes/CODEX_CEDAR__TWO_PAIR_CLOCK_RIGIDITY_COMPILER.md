# Exact two-pair clock rigidity and the finite gate compiler

## Current best attempt

**Reviewable claim.**  For two disjoint designated pairs in any finite
ordinary quitting profile, the sharp clock slack

```text
Delta = 1-sqrt(a)-sqrt(b)
```

has an exact nonnegative local-to-global ledger.  Positive-mass equality is
attained only by one symmetric pair gate followed by the other pair's sure
exit.  If `a,b>=alpha>0` and `Delta->0`, the same chronology is quantitatively
stable, including the one-player-deleted laws needed for Quit at the first
gate, Quit at the second gate, and Never.  Hence the entire saturated
arbitrary-clock strategic boundary reduces to two explicit one-parameter
finite all-behavior tests.

**Honest status and gap.**  Sections 1--7 below are reviewed ordinary
mathematics.  The input audit is
`feedback/INCENTIVE_GADGET_BREAKTHROUGH__BY_CODEX_CEDAR.md`; the independent
falsification of this repaired derivative is
`feedback/CODEX_CEDAR__TWO_PAIR_CLOCK_RIGIDITY_COMPILER__BY_CODEX_RAMSEY.md`.
The latter validates the mathematics after the two statement repairs now
incorporated below.  It does not produce a reward table forcing
`a,b>=alpha` and `Delta->0`, so it does not solve
`questions/INCENTIVE_GADGET.md` and remains internal under
`exports/README.md`.

**Sections to check.**  Section 2 is the exact ledger, Section 3 the equality
case, Section 4 the constants `2,10,10,6,36`, Section 5 the source-matched
one-player coupling, and Section 6 the exhaustive two-gate deviation table.

## 1. Setting, sources, and old versus new content

Let `I` be a nonempty finite set of players containing four distinct labels
`1,2,3,4`.  Put

```text
A={1,2},  B={3,4},  C=I\(A union B).
```

An ordinary behavioral profile in a quitting game is represented along its
unique live public history by numbers

```text
q_(t,i) in [0,1],  t in Nat, i in I,
```

where player `i` uses independent private randomization to Quit with
conditional probability `q_(t,i)` at date `t`.  Equivalently, the players'
planned first-Quit times are independent random variables in
`Nat union {Never}`.  The first nonempty quitting coalition absorbs.  There is
no public correlating device.

Let `a` be the probability that the strict first-quitter coalition is exactly
`A`, let `b` be the analogous probability for `B`, and put

```text
ell=1-a-b.
```

Thus `ell` includes all singletons, wrong pairs, larger coalitions,
calibrator-containing coalitions, and Never.

The inequalities

```text
sqrt(a)+sqrt(b)<=1,
ell>=2sqrt(ab),
ell^2>=4ab
```

are old independently reviewed conference mathematics.  They occur in
`notes/CODEX_CEDAR__INDEPENDENT_CLOCK_TOGGLE_GADGET.md` and in Propositions
17--18 of `notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`, reviewed in
`feedback/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL__BY_CODEX_NOETHER__ROUND_4.md`.

The external inputs for the present strengthening are

- `../infinite/INCENTIVE_GADGET_BREAKTHROUGH.md`;
- `../infinite/PAIR_CLOCK_RIGIDITY_COMPILER.md`; and
- `../infinite/TWO_GATE_STRATEGIC_REDUCTION.md`.

They supplied the square-root ledger and the proposed finite reduction.  This
note gives a self-contained proof, including the player-deleted coupling that
was only implicit there.  The genuinely new content is the exact slack
identity, the complete positive-mass equality classification, quantitative
near-equality rigidity, and the strategic reduction of the saturated branch.

For unrestricted deviations this note uses the checked theorem
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` from
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`: against
fixed opponents, deterministic Quit times and Never have the same payoff
supremum as all behavioral strategies.  The eventual negative semantic
consumer, if a reward producer supplies a fixed gap, is
`not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap` in
`UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.

## 2. Exact local and global slack ledgers

Write `c_(t,i)=1-q_(t,i)` and define the probability of reaching date `t` by

```text
S_t = product_(s<t) product_(i in I) c_(s,i),
z_t = sqrt(S_t).
```

Define survival-weighted target amplitudes

```text
x_t = z_t sqrt(q_(t,1)q_(t,2)c_(t,3)c_(t,4)
                   product_(j in C)c_(t,j)),
y_t = z_t sqrt(c_(t,1)c_(t,2)q_(t,3)q_(t,4)
                   product_(j in C)c_(t,j)).
```

Then, by disjointness of first-absorption dates,

```text
a=sum_t x_t^2,  b=sum_t y_t^2.                 (2.1)
```

### Proposition 2.1 (exact local budget)

For every date,

```text
x_t+y_t+z_(t+1)<=z_t.                          (2.2)
```

When `z_t>0`, put

```text
u=sqrt(c_(t,1)c_(t,2)),  v=sqrt(q_(t,1)q_(t,2)),
r=sqrt(c_(t,3)c_(t,4)),  s=sqrt(q_(t,3)q_(t,4)),
h=product_(j in C)sqrt(c_(t,j)).
```

Then `u+v<=1` and `r+s<=1` by the two-coordinate Cauchy inequality, while

```text
(x_t+y_t+z_(t+1))/z_t = h(vr+us+ur).
```

Moreover

```text
vr+us+ur = r(u+v)+us <= r+us <= r+s <=1.
```

This proves (2.2); if `z_t=0`, every term is zero.

Define

```text
e_t=z_t-z_(t+1)-x_t-y_t>=0.                    (2.3)
```

Direct expansion gives the two exact local ledgers

```text
e_t/z_t
 =(1-h)+h[(1-r-s)+r(1-u-v)+s(1-u)],            (2.4)

e_t/z_t
 =(1-h)+h[(1-u-v)+u(1-r-s)+v(1-r)]             (2.5)
```

when `z_t>0`.  Every term displayed on the right is nonnegative.  Thus the
defect separately records outside-player activity, unequal hazards within a
target pair, and simultaneous activity by incompatible target pairs.

### Theorem 2.2 (exact global slack decomposition)

Let

```text
X=sum_t x_t,  Y=sum_t y_t,  E=sum_t e_t,
z_infinity=lim_t z_t,
Delta=1-sqrt(a)-sqrt(b).
```

All series converge because (2.2) telescopes, and

```text
X+Y+E+z_infinity=1.                              (2.6)
```

With a zero-denominator fraction interpreted as zero,

```text
Delta
 =z_infinity+E
  +(X^2-a)/(X+sqrt(a))
  +(Y^2-b)/(Y+sqrt(b)).                           (2.7)
```

Indeed, nonnegativity gives `sqrt(sum x_t^2)<=sum x_t`, hence
`sqrt(a)<=X`, and similarly `sqrt(b)<=Y`.  Subtract
`sqrt(a)+sqrt(b)` from (2.6) and rationalize `X-sqrt(a)` and
`Y-sqrt(b)`.

Every term in (2.7) is nonnegative.  In particular `Delta>=0`, and

```text
ell-2sqrt(ab)
 =1-(sqrt(a)+sqrt(b))^2
 =Delta(1+sqrt(a)+sqrt(b)).                       (2.8)
```

This recovers the old clock inequality and identifies all of its slack.

## 3. Complete positive-mass equality classification

### Lemma 3.1 (local equality)

Suppose a reached date has `e_t=0` and `x_t+y_t>0`.  Exactly one target pair
is active.  If `x_t>0`, there is `p in (0,1]` such that

```text
q_(t,1)=q_(t,2)=p,
q_(t,j)=0 for every j notin A.                    (3.1)
```

The symmetric assertion holds if `y_t>0`.  In particular both amplitudes
cannot be positive at the same zero-defect date.

To prove this, assume `x_t>0` and use (2.4).  Equality forces `h=1`,
`r+s=1`, `r(1-u-v)=0`, and `s(1-u)=0`.  Since `x_t>0` gives `v,r>0`, one has
`u+v=1`; hence `u<1`, so `s=0`, `r=1`.  Equality in the two-coordinate
inequality `u+v<=1` gives `q_(t,1)=q_(t,2)`.  All outside hazards vanish.
The other case follows from (2.5).

The same calculation shows that a zero-defect date with `x_t=y_t=0` is the
all-Continue root: once `h=1`, the equality terms force either a positive
target amplitude or `u=r=1`.

### Theorem 3.2 (global equality)

Assume `a>0` and `b>0`.  Then `ell^2=4ab` if and only if, on its reached/live
chronology and perhaps after exchanging `A` with `B`, the profile is:

1. one date at which the two members of `A` independently Quit with the same
   probability `p in (0,1)`, while every other player Continues; and
2. conditional on both Continuing, one later date at which the two members
   of `B` Quit surely, while every other player Continues.

For this profile

```text
a=p^2,  b=(1-p)^2,  ell=2p(1-p).                 (3.2)
```

Proof.  Since `ell>=2sqrt(ab)` and both sides are nonnegative,
`ell^2=4ab` is equivalent to equality in (2.8), hence to `Delta=0`.
Equation (2.7) gives

```text
z_infinity=0,  e_t=0 for all t,
X^2-a=0,  Y^2-b=0.
```

But

```text
X^2-a=2 sum_(s<t)x_sx_t,
Y^2-b=2 sum_(s<t)y_sy_t.
```

Thus exactly one `x` date and one `y` date are positive.  Lemma 3.1 makes
them symmetric one-pair gates and every other **reached** date before
absorption all-Continue.  At the later gate, a hazard below one would leave
positive survival forever, contradicting `z_infinity=0`; it is therefore
sure.  Roots stored after that sure gate lie on zero-reach histories and are
arbitrary: the classification is modulo those null tails.  The first hazard
cannot be zero or one because both target masses are positive.  Formula
(3.2) follows.  The converse is immediate.

## 4. Quantitative stability and chronological concentration

Fix `alpha>0` and assume

```text
a,b>=alpha.                                       (4.1)
```

Choose dates `t_A,t_B` maximizing `x_t,y_t`.  A maximum exists because a
positive summable sequence cannot have a positive unattained supremum.

### Proposition 4.1 (temporal and survival bounds)

One has

```text
sum_(t!=t_A)x_t<=2Delta,
sum_(t!=t_B)y_t<=2Delta,                          (4.2)

E<=Delta,  Pr(Never)=z_infinity^2<=Delta^2.        (4.3)
```

If `t_A<t_B`, then

```text
Pr(absorption before t_A)<=10Delta,               (4.4)
Pr(absorption strictly between t_A and t_B)
  <=10Delta,                                      (4.5)
z_(t_B+1)<=6Delta,                                (4.6)
y_(t_B)>=sqrt(alpha)-2Delta.                       (4.7)
```

If `Delta<sqrt(alpha)/2`, the conditional all-Continue probability at the
later selected row is at most

```text
(6Delta/(sqrt(alpha)-2Delta))^2.                  (4.8)
```

Proof.  Put `m_A=max_t x_t`.  Since `a<=m_AX`,

```text
X-m_A <= (X^2-a)/X
       = (X-sqrt(a))(X+sqrt(a))/X
       <=2Delta.
```

The `Y` bound is identical, and (4.3) follows termwise from (2.7).

Before `t_A`, both amplitude sums omit their maxima, so (2.6) telescoped to
that date gives

```text
1-z_(t_A)
 <=2Delta+2Delta+Delta=5Delta.
```

Therefore `1-S_(t_A)<=2(1-z_(t_A))<=10Delta`.
Between the rows, telescope from `z_(t_A+1)` to `z_(t_B)`.  Again the `x`
sum omits `t_A`, the `y` sum omits `t_B`, and the `e` sum is at most
`Delta`.  Thus the square-root survival drop is at most `5Delta`, and the
probability drop is at most `10Delta`.  After the later row,

```text
z_(t_B+1)
 <=z_infinity+sum_(t>t_B)x_t+sum_(t>t_B)y_t+E
 <=Delta+2Delta+2Delta+Delta=6Delta.
```

Finally `y_(t_B)>=Y-2Delta>=sqrt(alpha)-2Delta`.  Since
`y_(t_B)<=z_(t_B)`, division and squaring prove (4.8).

### Theorem 4.2 (selected-subsequence rigidity)

Let profiles `sigma^n` satisfy (4.1) with one fixed `alpha>0` and
`Delta_n->0`.  After taking a subsequence, one of the following alternatives
holds on that selected subsequence:

- there are `t_n<s_n` and
  `p in [sqrt(alpha),1-sqrt(alpha)]` such that the reached root at `t_n`
  converges to `(p,p,0,0,0,...)` and the root at `s_n` converges to
  `(0,0,1,1,0,...)`; or
- the same statement holds with `A,B` exchanged.

Absorption before the first selected row and strictly between the rows tends
to zero; survival after the second row tends to zero.

Proof.  Pass to a subsequence on which `a_n->a_*` and `b_n->b_*`.  By (4.2),

```text
x_(t_A^n)->sqrt(a_*)>0,
y_(t_B^n)->sqrt(b_*)>0.
```

The selected dates cannot coincide eventually: `e_t/z_t->0` there while
both normalized target amplitudes stay positive, contradicting Lemma 3.1.
Choose one ordering; write it `t_n<s_n`.

Proposition 4.1 gives `z_(t_n)->1`.  Compactness of the finite root cube,
`e_(t_n)/z_(t_n)->0`, and Lemma 3.1 show that the first root converges to an
`A` gate `(p,p,0,...)`.  Since its amplitude converges to `sqrt(a_*)`,
`a_*=p^2`.

At the later row, the same argument gives a `B` gate with some common hazard
`q>0`.  Its pre-row survival stays bounded below because
`y_(s_n)>=sqrt(alpha)-o(1)`.  But (4.6) gives `z_(s_n+1)->0`; hence the
conditional Continue probability `(1-q)^2` is zero and `q=1`.  The survival
through the first gate and the vanishing middle absorption give
`z_(s_n)->1-p`, so `b_*=(1-p)^2`.  The two lower mass bounds yield
`p>=sqrt(alpha)` and `1-p>=sqrt(alpha)`.

The probability conclusions are (4.4)--(4.6).  Notice that an original
sequence may have subsequences of both orientations; the theorem asserts one
orientation on the subsequence selected here, not global uniqueness.

## 5. Source-matched one-player counterfactual convergence

The prescribed terminal-law convergence in Theorem 4.2 does not by itself
control a player's deleted clock: removing a preempting clock can reveal a
later opponent event.  This section proves the additional fact needed by the
strategic consumer.

### Theorem 5.1 (three pure-time ports)

Under the first orientation in Theorem 4.2, fix a player `i`.  Replace only
that player's strategy by one of

```text
Quit at t_n,  Quit at s_n,  Never.                 (5.1)
```

For each choice, the counterfactual terminal-coalition law converges in total
variation to the corresponding law in the literal two-stage profile
`G_(A->B)(p)`.  Consequently every bounded terminal reward coordinate has the
corresponding payoff limit.  The reverse orientation is symmetric.

Proof.  Couple every profile and its deviation by retaining all opponents'
planned Quit times.  Let `S_n^-` be opponent-only survival to the first row.
Since opponent survival is at least full survival,

```text
1-S_n^- <= 1-S_(t_n) ->0.                         (5.2)
```

Thus no opponent absorbs before `t_n`, with probability tending to one.

Let `L_n` be the prescribed probability of absorption strictly between the
selected rows.  Proposition 4.1 gives `L_n<=10Delta_n`.  Prescribed survival
immediately after the first row tends to `(1-p)^2>=alpha`.  Conditional
opponent absorption in the middle interval is therefore at most

```text
L_n/S_(t_n+1)=o(1).                               (5.3)
```

Deleting player `i` only removes one Continue factor.  If `i in A`, the
ratio of counterfactual to prescribed reach just after the first row is

```text
[product_(u<t_n)c_(u,i)]^(-1) [1-q_(t_n,i)]^(-1)
  ->1/(1-p)<=1/sqrt(alpha).                       (5.4)
```

The first factor tends to one by the full pre-gate survival bound (and also
follows by combining that bound with (5.2)).  If `i notin A`, the ratio tends
to one.  Thus the unconditional middle bad-event probability under Quit at
`s_n` or Never is still `o(1)`.  Quit at `t_n` terminates at the first row.

At `t_n`, the opponents' independent Bernoulli vector converges
coordinatewise to the `A` gate with player `i` deleted; adjoining the
deviator's deterministic action therefore gives the literal first-row
coalition distribution.  On the all-Continue branch, (5.3)--(5.4) transport
the play to `s_n` without another exit, up to `o(1)` probability.

At `s_n`, the opponents' root converges to the sure `B` gate with player `i`
deleted.  If `i notin B`, both `B` members remain and absorb.  If `i in B`,
the other `B` member remains and absorbs.  Hence under Never the probability
of surviving beyond `s_n` tends to zero.  Quit at `s_n` terminates at that
row by definition.

There are finitely many terminal coalitions.  The probability of every
history outside the two selected rows is `o(1)`, while the two row vectors
converge coordinatewise.  The complete counterfactual terminal law therefore
converges in total variation.  Bounded rewards give payoff convergence.

The positive lower bound on both target masses is essential to the uniform
reach comparison (5.4); without it the Continue probability `1-p` may vanish
and deletion of a first-gate member can magnify a hidden middle law.

## 6. Exact finite two-gate strategic consumer

Fix `p in [0,1]`.  In `G_(A->B)(p)`, players 1 and 2 independently Quit at
date zero with probability `p`, and everyone else Continues.  Conditional on
both Continuing, players 3 and 4 Quit surely at date one and everyone else
Continues.  Absorption is certain by date one, with probabilities

```text
Pr(A)=p^2,
Pr({1})=Pr({2})=p(1-p),
Pr(B)=(1-p)^2.                                    (6.1)
```

For a reward table `r`, every player's prescribed payoff is

```text
U_i(p)=p^2 r_i(A)
       +p(1-p)[r_i({1})+r_i({2})]
       +(1-p)^2 r_i(B).                           (6.2)
```

Every deterministic Quit time is equivalent to Quit at date zero, Quit at
date one, or Never.  Their values are as follows.

For player 1,

```text
Q^0_1=p r_1(A)+(1-p)r_1({1}),
Q^1_1=p r_1({2})+(1-p)r_1({1,3,4}),
N_1  =p r_1({2})+(1-p)r_1(B).                    (6.3)
```

For player 2, exchange 1 and 2:

```text
Q^0_2=p r_2(A)+(1-p)r_2({2}),
Q^1_2=p r_2({1})+(1-p)r_2({2,3,4}),
N_2  =p r_2({1})+(1-p)r_2(B).                    (6.4)
```

For player 3,

```text
Q^0_3=p^2 r_3({1,2,3})
      +p(1-p)[r_3({1,3})+r_3({2,3})]
      +(1-p)^2r_3({3}),
Q^1_3=U_3,
N_3  =p^2r_3(A)
      +p(1-p)[r_3({1})+r_3({2})]
      +(1-p)^2r_3({4}).                           (6.5)
```

For player 4, exchange 3 and 4:

```text
Q^0_4=p^2 r_4({1,2,4})
      +p(1-p)[r_4({1,4})+r_4({2,4})]
      +(1-p)^2r_4({4}),
Q^1_4=U_4,
N_4  =p^2r_4(A)
      +p(1-p)[r_4({1})+r_4({2})]
      +(1-p)^2r_4({3}).                           (6.6)
```

For an outsider `c in C`,

```text
Q^0_c=p^2r_c(A union {c})
      +p(1-p)[r_c({1,c})+r_c({2,c})]
      +(1-p)^2r_c({c}),
Q^1_c=p^2r_c(A)
      +p(1-p)[r_c({1})+r_c({2})]
      +(1-p)^2r_c(B union {c}),
N_c  =U_c.                                        (6.7)
```

Define

```text
g_i(p)=max(Q^0_i(p),Q^1_i(p),N_i(p))-U_i(p),
Expl_(A->B)(p)=max_(i in I) g_i(p).               (6.8)
```

For gate players the prescribed strategy is a mixture of Quit 0 and Never,
for backup players it is Quit 1, and for outsiders it is Never.  Hence
`g_i>=0`.  Every listed function is a polynomial of degree at most two, so
`Expl_(A->B)` is continuous, piecewise quadratic, and semialgebraic.  Define
`Expl_(B->A)` by exchanging the two pairs.

The pure-time extremality theorem cited in Section 1 shows that (6.8) is the
exact exploitability against unrestricted unilateral behavioral deviations,
not merely against the three displayed actions.

For an arbitrary actual profile `sigma`, define

```text
Expl(sigma)
 =max_(i in I) [sup_(behavioral deviations tau_i)
       U_i(update(sigma,i,tau_i))-U_i(sigma)].           (6.9)
```

The supremum is finite because the reward table is finite and bounded.  By
the same checked pure-time extremality theorem it is equivalently the maximum
of the pure-time best-response gains.

### Theorem 6.1 (boundary zero extraction)

Let `sigma^n` be actual behavioral profiles with

```text
a_n,b_n>=alpha>0,  Delta_n->0,
Expl(sigma^n)->0.                                 (6.10)
```

Then one of the two functions `Expl_(A->B)` and `Expl_(B->A)` has a zero at
some `p in [sqrt(alpha),1-sqrt(alpha)]`.

Proof.  Apply Theorems 4.2 and 5.1.  The prescribed terminal law converges to
the literal gate law, so every `U_i` converges.  Each of the three literal
pure-time values is the limit of its source-matched counterfactual value.
Every limiting deviation gain is therefore nonpositive by (6.10).  But the
literal gate's exact exploitability (6.8) is nonnegative, so it is zero.

### Corollary 6.2 (finite gate consumer)

If a reward table and constants `alpha,kappa>0` satisfy

```text
min_(p in [sqrt(alpha),1-sqrt(alpha)]) Expl_(A->B)(p)>=kappa,
min_(p in [sqrt(alpha),1-sqrt(alpha)]) Expl_(B->A)(p)>=kappa.              (6.11)
```

then no sequence can satisfy (6.10).  Thus a saturated arbitrary-clock branch
is consumed by two finite one-dimensional semialgebraic checks.

This is a verifier/consumer for a near-saturated actual clock sequence.  It
does not produce that sequence or show that low exploitability forces its
hypotheses.

## 7. Boundary tests and exact remaining gap

### 7.1 Positive equality test

The literal profile `G_(A->B)(p)` for `0<p<1` has

```text
(a,b,ell)=(p^2,(1-p)^2,2p(1-p)),  Delta=0.
```

It realizes every equality conclusion, including the sure later gate.

### 7.2 Each defect is necessary

- If an outside player has positive hazard at a reached row, `1-h>0` in
  (2.4)--(2.5).
- If a target pair uses unequal hazards, the corresponding Cauchy slack is
  positive.
- If both target pairs are active at one row, the final cross term in one of
  the ledgers is positive.
- If one target amplitude is positive at two dates, its temporal defect
  contains the positive term `2x_sx_t`.
- Positive Never mass contributes the separate term `z_infinity`.

Thus none of the four global defect types may be omitted from the equality
classification.

### 7.3 Strategic formula test

Let all rewards be zero except `r_1({1})=1`.  In the orientation `A->B`,

```text
U_1=p(1-p),  Q^0_1=1-p,
Q^0_1-U_1=(1-p)^2.
```

On `p<=1-sqrt(alpha)` the finite consumer detects gain at least `alpha`.
This is only a check of the deviation formula, not an incentive gadget: the
reverse orientation and the producer hypotheses are not supplied.

### 7.4 Remaining conjecture-facing obligation

The maintained `INCENTIVE_GADGET` question asks for one rational table whose
low-error profiles are forced into incompatible pair-atom and leakage bounds,
or for a universal negative theorem about such tables.  Nothing here supplies
either.  The exact remaining boundary is:

1. produce from the reward table a fixed `alpha>0` and an actual low-
   exploitability sequence with `a,b>=alpha` and `Delta->0` (or derive an
   immediate gap off that branch); and
2. prove the two finite functions in (6.11) are uniformly positive.

The reviewed direct all-ranks watchdog architecture remains blocked by its
grand-coalition sure-exit sink.  The present theorem neither reopens nor
resolves that architecture.

## Independent review and disposition

`feedback/CODEX_CEDAR__TWO_PAIR_CLOCK_RIGIDITY_COMPILER__BY_CODEX_RAMSEY.md`
checks the zero-amplitude equality case, null-history qualification, all
constants and date indices, the player-deleted coupling, every finite gate
formula, and unrestricted pure-time reduction.  Verdict: PASS after the two
statement repairs incorporated above.

The same review rejects export promotion.  The note is a conditional
sharp-saturation verifier whose actual source hypothesis remains open.  It
answers neither accepted arm of `questions/INCENTIVE_GADGET.md`, so it stays
in `notes/` unless later work constructs or excludes the near-saturated
source from actual reward data.
