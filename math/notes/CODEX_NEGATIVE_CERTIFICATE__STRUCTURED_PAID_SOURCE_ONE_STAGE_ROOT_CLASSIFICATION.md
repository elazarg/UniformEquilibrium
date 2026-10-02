# Exact roots at a structured stationary paid source force debt descent

Author: `CODEX_NEGATIVE_CERTIFICATE`

## Status

**Exact ordinary mathematics; not checked in Lean and not proposed for
export.**  This note classifies every exact one-stage product Nash root against
the literal prescribed payoff of the structured stationary paid source.  The
only possible zero-debt-drop limit is a root with the paid player surely
quitting.  The source cap pin then turns that root into terminal approximate
Nash profiles against complete behavioral deviations, contradicting the
standing no-uniform-payoff branch.  Consequently every exact root at the
source produces a uniform positive terminal-semantic debt drop.

The conclusion is source-specific.  It uses simultaneously the paid player's
fixed debt, the limiting equality of its complete cap with its solo reward,
and the positive **global** minimum debt.  It does not claim that an arbitrary
paid port has the same property or that the resulting one-step descent is
renewable.

## Exact question

Let `I=Fin 4`, and let `tau_n` be the final actual stationary source supplied
by the reviewed tropical chronology.  Put

```text
X_n=(u_n,B_n)=quittingTerminalSemanticPair reward tau_n,
d_(n,i)=B_(n,i)-u_(n,i),
D_n=sum_i d_(n,i).
```

Fix the final Quit-now mover `b`.  On a common tail there is `gamma>0` such
that

```text
d_(n,b)>=gamma,
B_(n,b)->s_b:=reward({b})_b.                              (1)
```

The first identity uses the complete behavioral cap: Quit at date zero is the
exact cap at `tau_n`.  In particular

```text
limsup_n u_(n,b)<=s_b-gamma.                              (2)
```

Assume the game has no uniform-equilibrium payoff.  Hence there are a
terminal exploitability gap `Gamma>0` and a positive global carrier minimum

```text
D_*>0,
D_*<=D(X) for every terminal-semantic carrier point X.     (3)
```

For each `n`, let `q_n` be any exact independent one-stage Nash root against
the **literal payoff tail** `u_n`.  The structured stationary Quit margin
gives one common absorption floor

```text
Abs(q_n)>=a>0                                             (4)
```

for every such root and all large `n`.  Equivalently, (4) may be taken as the
already proved input from the structured-port exactification barrier.

Does the finite support of a limit root necessarily yield a terminal/product
equilibrium, a sole-owner reset, or a counterexample to that dichotomy?

## Exact statement

Under (1)--(4), there are `delta>0` and `N` such that for every `n>=N` and
every exact product Nash root `q` against `u_n`,

```text
D(X_n)-D(Prefix(q,X_n)) >= delta.                        (5)
```

Here `Prefix(q,X_n)` is the exact terminal-semantic prefix, so (5) concerns
complete behavioral caps after the literal root is placed before `tau_n`.

More precisely, if a sequence of such roots had debt drop tending to zero,
its coalition support would pass through the following exhaustive Fin4
classification:

1. collision mass tends to zero;
2. every singleton mass owned by `k!=b` tends to zero;
3. the fixed absorption charge therefore concentrates on singleton `{b}`;
4. exact root complementarity and (2) force `b` to Quit surely; and
5. (1) then makes the actual root/`tau_n` splices terminal
   `epsilon_n`-equilibria with `epsilon_n->0` and payoff tending to
   `reward({b})`.

The last item contradicts the terminal gap.  Thus the sole-owner unscreened
reset boundary is algebraically real but cannot occur at this structured
source: an owner different from `b` is excluded by `d_(n,b)>=gamma`, while a
genuinely mixed owner `b` is excluded by `u_(n,b)<s_b`.

## Definitions and assumptions

For an independent Boolean root `q`, write

```text
mu_q(S)=prod_(i in S) q_i prod_(i notin S)(1-q_i),
Abs(q)=sum_(S nonempty) mu_q(S),
Coll(q)=sum_(|S|>=2) mu_q(S).
```

The five Fin4 coalition buckets used below are

```text
Coll(q), mu_q({b}), and mu_q({k}) for the three k!=b.      (6)
```

They sum to `Abs(q)`.  No correlated coalition lottery is introduced.

For a carrier pair `X` and an exact root `q` at its prescribed coordinate,
put

```text
Drop(X,q)=D(X)-D(Prefix(q,X)).                            (7)
```

All semantic caps in (7) are suprema over unrestricted behavioral
deviations, including Never and arbitrary late or randomized clocks.

The proof uses no punishment-floor inequality for `u_n`.  This is important:
the paid coordinate may satisfy `u_(n,b)<s_b` while punishment normality gives
only `P_b<=s_b`, not `P_b<=u_(n,b)`.

## Proof

### 1. Exact prefix inequalities

Exact root prefixing cannot increase coordinate debt.  Two checked
consequences give, for every `n`,

```text
D_* Coll(q_n) <= Drop(X_n,q_n),                          (8)
mu_(q_n)({k}) d_(n,j) <= Drop(X_n,q_n)   when j!=k.      (9)
```

Equation (8) uses the global lower bound (3), not merely the local paid debt.
Equation (9) says that absorption by one owner screens every other player's
tail debt by exactly the corresponding singleton mass.  Both inequalities
are for the complete terminal-semantic prefix.

Suppose toward contradiction that a subsequence, relabeled by `n`, satisfies

```text
e_n:=Drop(X_n,q_n)->0.                                   (10)
```

From (8) and `D_*>0`,

```text
Coll(q_n)->0.                                            (11)
```

For each of the three labels `k!=b`, use (9) with `j=b` and (1):

```text
gamma mu_(q_n)({k}) <= e_n,
mu_(q_n)({k})->0.                                        (12)
```

The exact five-bucket decomposition (6), (4), and (11)--(12) now give

```text
liminf_n mu_(q_n)({b})>=a.                               (13)
```

Thus the zero-drop support is not an arbitrary solo owner: its fixed owner is
the already paid label `b`.

### 2. Product support forces all opponents out

Pass to a root-simplex subsequence.  Formula (13) gives `q_(n,b)>=a/2` and
positive probability that every opponent Continues for all large `n`.  For
each `j!=b`,

```text
mu_(q_n)({b,j})/mu_(q_n)({b})=q_(n,j)/(1-q_(n,j)).       (14)
```

The numerator is at most `Coll(q_n)`.  Equations (11), (13), and (14) imply

```text
q_(n,j)->0   for every j!=b.                             (15)
```

This is the product-law step.  Collision mass zero for a general correlated
coalition lottery would not force (15).

### 3. The paid endpoint forces a sure quitter

Let `Q_(n,b)` and `C_(n,b)` be player `b`'s forced Quit and forced Continue
payoffs in the one-stage game with opponent root `q_(n,-b)` and continuation
value `u_(n,b)`.  Bounded rewards, (2), and (15) give

```text
liminf_n (Q_(n,b)-C_(n,b))>=gamma.                       (16)
```

Indeed the two endpoints tend respectively to `s_b` and a limit at most
`s_b-gamma`.  For large `n`, (13) also gives `q_(n,b)>0`.  Exact binary Nash
complementarity says Quit is optimal when it has positive support, and says
Continue is optimal whenever `q_(n,b)<1`.  The strict inequality in (16)
therefore forces

```text
q_(n,b)=1                                                (17)
```

for every sufficiently large `n`.

This is where the apparent mixed sole-owner reset disappears.  A genuinely
mixed solo owner must be indifferent between its solo reward and its literal
tail.  The structured source instead has a fixed strict gap between those
two quantities.

### 4. Complete tail screening at the pure-`b` boundary

Because of (17), every opponent `j!=b` faces a sure quitter even after an
arbitrary unilateral behavioral replacement.  Its continuation behavior is
never reached.  Changing the one-stage continuation annotation from `u_n` to
the complete cap vector `B_n` therefore preserves all three outsiders' exact
root inequalities.

Only `b` can remove the last sure quitter.  Against the cap tail, its possible
extra endpoint gain is

```text
zeta_n=[C_b(q_(n,-b);B_(n,b))-Q_b(q_(n,-b))]_+.          (18)
```

Equations (1) and (15) imply

```text
Q_b(q_(n,-b))->s_b,
C_b(q_(n,-b);B_(n,b))->s_b,
zeta_n->0.                                               (19)
```

Hence `q_n` is a `zeta_n`-Nash root against the vector of unrestricted
continuation caps of the literal tail `tau_n`.  The checked sure-first-stage
compiler now gives

```text
q_n then tau_n is a terminal zeta_n-equilibrium          (20)
```

against every behavioral deviation.  Its prescribed terminal law converges
to the pure singleton `{b}` by (15) and (17), so its payoff converges to the
fixed vector `reward({b})`.

The standing terminal exploitability gap `Gamma>0` contradicts (20) once
`zeta_n<Gamma`.  Equivalently, the fixed-target terminal compiler would make
`reward({b})` a uniform-equilibrium payoff.  This contradiction proves that
(10) is impossible.

### 5. Uniformization over all exact root selections

The drops are nonnegative.  If (5) failed, for every positive integer `m`
one could choose `n_m>=m` and an exact root at `u_(n_m)` whose drop is less
than `1/m`.  Finite-game Nash existence supplies roots, and this diagonal
choice would satisfy (10), contradicting Sections 1--4.  Therefore one
common `delta>0` and tail index `N` work for **every** exact root selection.

This proves (5).

## The sole-owner boundary and why it is absent here

The classification also identifies exactly what would survive without the
two source pins in (1).  Suppose a zero-drop charged limit were the solo root
of owner `k` with rate `p>0`.

- Equations (9) force every debt except possibly `d_k` to vanish.
- If `0<p<1`, root complementarity forces the literal equality
  `u_k=s_k`.  Player `k`'s root-Continue branch reaches the old source with
  probability `1-p`, and its complete continuation gain is the unscreened
  owner debt `d_k>=D_*`.  This is a genuine source-attached paid/reset
  object, not a terminal equilibrium.
- If `p=1`, the root is terminally screened exactly when `B_k<=s_k`.
  If `B_k>s_k`, player `k` obtains the exact source-reset gain
  `B_k-s_k` by Continuing at the root and then using a complete best response
  in the literal tail.

At the structured port, `k!=b` is impossible because (1) leaves the fixed
positive `b` debt, while mixed `k=b` is impossible by (2).  The remaining
pure `k=b` endpoint has `B_b->s_b` and is therefore the tail-screened branch
of Sections 3--4.  No third regression survives all the structured fields.

## Boundary and falsification tests

1. **Drop the positive global minimum.**  Equation (8) no longer removes
   collision mass.  A collision-supported exact root can retain fixed charge
   while the displayed local debt inequalities say nothing.  Thus local cap
   separation is not a substitute for `D_*>0`.
2. **Drop the fixed paid debtor.**  A singleton owner `k!=b` can carry the
   charge with all debt concentrated on `k`; (12) no longer selects `b`.
3. **Drop the strict prescribed-payoff gap.**  If `u_b=s_b` and
   `0<q_b<1`, the mixed solo-`b` root is exact and its all-Continue branch
   preserves the whole owner debt.  This is the unscreened reset boundary.
4. **Drop the cap pin.**  A pure-`b` root with `B_b>s_b` is not terminally
   screened.  The missing gain is exactly `B_b-s_b`, realized by Continue
   followed by a complete tail best response.
5. **Use only prescribed-payoff Nash.**  A sure quitter does not by itself
   screen that quitter's own continuation deviation.  Equation (18), using
   the complete cap, is indispensable.
6. **Correlated roots.**  The ratio (14) is a product identity.  The theorem
   does not cover public correlation over quitting coalitions.

The Solan--Vieille paid-port regression does not contradict this theorem: its
global minimum is zero, so the collision estimate (8) has no coercive content.

## Source correspondence

The structured source, fixed Quit-now debt, cap pin, literal stationary tail,
and source chronology are in
[`CODEX_SNELL__TROPICAL_SUPPORT_FOUR_TWO_OWNER_ENDPOINT_EXIT.md`](CODEX_SNELL__TROPICAL_SUPPORT_FOUR_TWO_OWNER_ENDPOINT_EXIT.md)
and the reviewed composition staged as
`FIN4_TROPICAL_TWO_NEVER_TO_OFFMINIMUM_PAID_PORT.md`.
The uniform root-absorption floor against the literal payoff tail is proved in
Section 8 of
[`CODEX_SPINOZA__STRUCTURED_STATIONARY_PAID_PORT_EXACTIFICATION_BARRIER.md`](CODEX_SPINOZA__STRUCTURED_STATIONARY_PAID_PORT_EXACTIFICATION_BARRIER.md).

The checked exact-prefix inequalities are

```text
quittingTerminalSemanticDebtDrop_nonneg_of_exact
lowerDebt_mul_collisionMass_le_debtDrop_of_exact
singletonMass_mul_otherDebt_le_debtDrop_of_exact
```

in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourOffMinimumChargedBlockerGate.lean`.
The five-bucket absorption identity is
`quittingRootAbsorptionMass_eq_sum_singletonMass_add_collisionMass`.

The all-behavior first-stage bridge is

```text
isεAsymptoticNash_quittingRootThenContinuation_of_isεQuittingRootNash
```

in `UniformEquilibrium/Quitting/Root/FirstBranch.lean`; it tests the root
against `quittingContinuationBestResponse`, not merely the prescribed payoff.
Tail independence under a remaining sure quitter is
`quittingRootExpectedPayoff_eq_of_hasSureQuitter`.  Joint root/tail Nash-defect
continuity is in
`UniformEquilibrium/Quitting/Root/NashDefectContinuity.lean`.

The earlier general zero-drop theorem
`exists_macroscopicDebtDrop_or_chargedSoloBlockerGate` requires a
punishment-floor tail in order to manufacture its synthetic blocker tail.
The present source-specific argument does not invoke that unavailable floor.
Instead, the fixed debtor and cap pin eliminate the solo gate before any
synthetic continuation is introduced.

No external literature result is used.

## Conjecture-facing consequence

At the structured stationary tropical port, finite mixed-Nash existence no
longer gives merely a charged payoff-tail entrance.  Prefixing **any** exact
root selected against the actual source payoff decreases complete
terminal-semantic debt by a fixed amount.  The alternative zero-drop support
would itself give terminal approximate equilibria with a fixed target and is
therefore impossible in the no-uniform branch.

This is stronger than a local cap-separation rectangle: the root and the
literal tail are co-realized, and the drop is computed on their actual
terminal-semantic prefix.  It remains weaker than a renewable rank.  After
the one prefix, the new prescribed payoff need not be another structured
stationary port, so the theorem cannot simply be reapplied.

## Scope and nonclaims

- The theorem is ordinary mathematics, not yet Lean-checked.
- It classifies independent product roots against the literal payoff `u_n`,
  not roots against the cap tail `B_n` or a synthetic clipped vector.
- The exact root covers only current one-stage deviations; complete
  behavioral semantics enter through the terminal-semantic prefix identities
  and the cap-tail first-stage compiler.
- The terminal/product equilibrium appears only in the forbidden zero-drop
  limit.  The actual no-uniform conclusion is the uniform debt drop (5).
- No punishment-floor admissibility of `u_n` is assumed or inferred.
- The new prefix is an actual carrier point but is not proved to regenerate a
  stationary source, the tropical ancestry, a minimum passport, or a paid
  row with the original labels.
- One macroscopic debt drop does not by itself yield a uniform-equilibrium
  payoff or decide the Fin4 conjecture.

## Concrete next check

Independently falsify the two source-specific steps: the selection of `b` from
the five coalition buckets via (9), and the upgrade from sure-`b` payoff-tail
Nash to cap-tail approximate Nash in (18)--(20).  If both pass, the natural
Lean handoff is a theorem adjacent to
`exists_macroscopicDebtDrop_or_chargedSoloBlockerGate` which accepts the
fixed-debtor/cap-pin source sequence and returns the uniform bound (5), without
a punishment-floor hypothesis.
