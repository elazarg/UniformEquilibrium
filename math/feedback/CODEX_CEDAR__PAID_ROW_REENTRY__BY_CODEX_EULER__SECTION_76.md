# Review of Proposition 76 and Corollaries 76A--B

Reviewer: `CODEX_EULER`

Verdict: **PASS after one applied literal counting repair.**  The
expectation/atom constants, endpoint-incidence split, source quantifiers,
floor-safe Proposition 73 handoff, collision-mass alternative, stationary
identity, product-coupling estimate, and exact-edge/source-event dichotomy are
all mathematically correct.  One sentence after Proposition 76 says “exactly
these four incidence types,” but the displayed split has five types:

```text
immediate high: singleton {j} / collision containing j;
Never high:     Never / singleton {k}, k!=j / collision disjoint from j.
```

Replace “four” by “five,” or simply say “the listed incidence types.”  No
other repair is required.

## Proposition 76: source-matched atom

The accepted Section 75 source supplies an actual stationary profile `tau`,
a free debtor `j`, and attained pure endpoints immediate Quit and Never with

```text
max(Q_j,N_j)-U_j(tau)>=Gamma.
```

Thus the selected high endpoint is a literal unilateral replacement preserving
every opponent law; no supremum attainment is being added.

Let `G` consist of terminal outcomes whose `j`-reward is at least
`U_j+Gamma/2`, and let `p=Pr(G)`.  Since `H>=U_j+Gamma` and every reward and
`U_j` lie in `[-M,M]`,

```text
U_j+Gamma
  <= p*M+(1-p)*(U_j+Gamma/2)
```

implies

```text
Gamma/2 <= p*(M-U_j-Gamma/2) <= 2M*p,
p>=Gamma/(4M).
```

There are exactly `2^n` terminal outcomes after including Never, so one has
mass at least

```text
alpha=Gamma/(4M*2^n)
```

and reward premium at least `Gamma/2`.  Under immediate Quit, the date-zero
coalition contains `j`; under Never, no absorbing coalition contains `j`.
The five displayed incidence types are therefore exhaustive and source
matched.

## Corollary 76A: singleton stack or collision mass

In the floor-safe immediate-Quit arm, if

```text
r({j})_j-U_j>=Gamma/2,
```

the exact hypotheses of reviewed Proposition 73 hold at
`X^0=Sem(tau)`, with `g=j`, `Delta=Gamma/2`, and hence
`delta=Delta/2=Gamma/4`.  Its fixed root-charge constant is exactly

```text
c=delta/(delta+2M)=Gamma/(Gamma+8M).
```

The source is an attained behavioral semantic pair, not merely a compact
cluster, and `U>=P` supplies the floor entrance.  Proposition 73 therefore
constructs literal source-matched exact floor predecessors and its reviewed
finite collision-budget alternative; Corollary 73A consumes any infinite
recurrence of the fixed charge into the maintained near-return.

If the singleton inequality fails, every good outcome under immediate Quit
must be a collision containing `j`.  The whole good-set probability is at
least `Gamma/(4M)`, proving the total first-row collision bound, and the
pigeonholed collision retains the atom bound `alpha`.  This is behavioral
first-row event mass, not exact Bellman charge.

## Corollary 76B: exact root or source collision

For the stationary source row `p`, let `x=p_j`, let `Q,C` be `j`'s forced
action endpoints at the stationary tail `U`, and put

```text
h=1-product_(k!=j)(1-p_k).
```

Stationarity gives `U_j=xQ+(1-x)C`.  Immediate Quit being high gives
`Q-U_j>=Gamma`; therefore `x<1` and

```text
Q-C=(Q-U_j)/(1-x)>=Gamma.
```

Choose any exact product Nash root `q` at tail `U`.  If `q_j=1`, its
absorption is one.  Otherwise Continue has positive support, so exact Nash
gives `Quit(q)-Continue(q)<=0`.  Couple the opponent product rows of `p` and
`q`.  Each forced-action payoff changes by at most

```text
2M*sum_(k!=j)|q_k-p_k|,
```

so the action-gap change is at most twice that amount.  Hence

```text
sum_(k!=j)|q_k-p_k|>=Gamma/(4M).
```

With

```text
c0=Gamma/[8M(n-1)],
```

the terminal witness gives `n>=2`, and payoff boundedness gives
`Gamma<=2M`, so `c0` is well defined and positive.  If `h<c0`, every
`p_k<=h`, whence

```text
sum p_k<Gamma/(8M),
sum q_k>=Gamma/(8M).
```

Some opponent marginal of `q` is at least `c0`, and joint absorption
dominates that marginal.  Thus either `h>=c0` or
`absorption(q)>=c0`, with the claimed constant.

Because `U>=P`, finite mixed Nash supplies such an exact root and the checked
floor-forward inequality makes prefixing `Sem(tau)` by it a genuine exact
punishment-floor Bellman edge.  In contrast, `h` is exactly the source
collision probability only in the literal immediate-Quit receiving profile.
The statement correctly keeps these interfaces separate.

## Scope

The Section 75 quantifiers are retained exactly: `tau` is the repaired actual
stationary source, `j` is a free debtor distinct from the retained owner, and
the high endpoint is one of two attained pure-time laws.  Only the floor-safe
immediate-Quit singleton subbranch enters Proposition 73 directly.

Never, a distinct singleton owner, and the nonsingleton atom alternatives are
behavioral source events.  They do not provide an exact simultaneous root,
Bellman charge, repayment, tangent rank, or payoff near-return.  The
incidence-count wording repair has been applied.  No mathematical or scope
objection remains.
