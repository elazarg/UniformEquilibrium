# Fin4 hard residual versus Simon normalized motion

Author: `CODEX_MINER`

Status: `ORDINARY-MATHEMATICS NEGATIVE CONNECTOR; AWAITING INDEPENDENT REVIEW`

The constrained stationary roots which produce the quantitative full-support
packet do **not** produce the small normalized motion required by the reviewed
Simon stationary-prefix theorem.  On the compact-limit subsequence, every
tail which makes those full-support rows support-locally optimal has normalized
motion converging to the packet's singleton surplus.  A terminal
exploitability witness makes that surplus nonzero, uniformly away from zero in
packet-defect units.  Thus the actual residual source lands on Simon's fixed-
rho failure side.

This is a route decision, not a proof of the Fin4 conjecture.  The positive
result found by the accompanying note crawl is the separately reviewed
singleton-base source in
[`CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT.md`](CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT.md),
Sections 1--9.  Its Corollary 4.3 has a direct same-law arrow from the actual
hard residual into the checked fixed-law reset dispatcher.  That is the
conjecture-facing formalization candidate; the Simon calculation below is a
negative screen and should not be exported as a purported producer.

## 1. Exact question and source boundary

Let `reward` be a bounded quitting reward table on a nonempty finite player
set.  For a product row `p`, write

```text
q(p) = probability that at least one player Quits,
f(r,p) = one-stage expected payoff with tail r after joint Continue.
```

When `q(p)>0`, let `h(p)` be the conditional payoff of the absorbing event in
one row.  Then, coordinatewise,

```text
f(r,p)-r = q(p) * (h(p)-r).                         (1.1)
```

For player `i`, write

```text
c_i(p) = product_(j != i) (1-p_j),
g_i(r,p) = forcedQuit_i(r,p)-forcedContinue_i(r,p).
```

Forced Quit absorbs immediately and is independent of `r_i`; forced Continue
uses `r_i` exactly on the event that every opponent Continues.  Therefore

```text
g_i(r,p)=g_i(h(p),p)+c_i(p)*(h_i(p)-r_i).            (1.2)
```

The checked full-support lift in
`NormalTerminalGapConstrainedStationary.lean` supplies roots `p^n` with:

* positive total marginal hazard tending to zero;
* every normalized marginal bounded below by one fixed positive constant;
* every marginal strictly between zero and one for large `n`; and
* `g_i(h(p^n),p^n)<=0` for every player.

After a subsequence, their normalized marginal directions converge to the
mass `mu` of the produced full-support singleton packet.  Since all packet
masses are positive, its target is the own-singleton vector

```text
s_i=reward({i})_i.
```

Put

```text
z_i=sum_j mu_j reward({j})_i,
e_i=z_i-s_i.                                         (1.3)
```

The packet inequalities say `e_i>=0`.  The question is whether the same roots,
with a suitable tail, satisfy the hypotheses of Proposition 44 in
`CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`, exported as
[`SIMON_NORMALIZED_MOTION_STATIONARY_PREFIX_PRODUCER.md`](../exports/SIMON_NORMALIZED_MOTION_STATIONARY_PREFIX_PRODUCER.md).

## 2. First-order limit of the actual roots

### Lemma 2.1 (stationary conditional payoff and endpoint limit)

Along the selected compact-limit subsequence,

```text
h_i(p^n) -> z_i,
c_i(p^n) -> 1,
g_i(h(p^n),p^n) -> -e_i.                             (2.1)
```

#### Proof

Let `H_n=sum_i p_i^n`.  The one-row absorption probability satisfies

```text
H_n-O(H_n^2) <= q(p^n) <= H_n.
```

The probability of singleton `{j}` is

```text
p_j^n * product_(k != j)(1-p_k^n),
```

so after division by `q(p^n)` its limit is `mu_j`.  The collision probability
is `O(H_n^2)`, hence its conditional mass is `O(H_n)`.  Bounded rewards then
give `h_i(p^n)->z_i`.

If player `i` is forced to Quit, the opponents' hazards vanish, so its payoff
tends to `reward({i})_i=s_i`.  If it is forced to Continue, the current-row
opponent absorption contribution tends to zero, while the all-opponents-
Continue coefficient tends to one and the tail `h_i(p^n)` tends to `z_i`.
Thus the endpoint difference tends to `s_i-z_i=-e_i`.

Equivalently, the last limit follows directly from the checked comparison

```text
abs_quittingRootEndpointDifference_add_singletonLCPResidual_le
```

in `NormalTerminalGapFullSupportCompactLimit.lean`: the error is at most a
fixed reward-bound multiple of the total hazard, and the singleton-LCP
residual converges to `e_i`.  QED.

## 3. Every support repair retains the packet surplus

### Proposition 3.1 (support-local tails cannot have small normalized motion)

Let `gamma_n>=0` tend to zero, and let `r^n` be any tails for which `p^n` is
support-locally `gamma_n`-optimal.  Then

```text
h_i(p^n)-r_i^n -> e_i                                (3.1)
```

for every player, and consequently

```text
||f(r^n,p^n)-r^n||_infinity / q(p^n)
  -> max_i e_i.                                      (3.2)
```

In particular, if the packet has positive singleton surplus in any
coordinate, these rows cannot satisfy

```text
||f(r^n,p^n)-r^n||_infinity < gamma_n q(p^n).
```

#### Proof

For large `n`, every player's Quit and Continue actions both have positive
probability.  Support-local `gamma_n`-optimality therefore gives both endpoint
inequalities and hence

```text
|g_i(r^n,p^n)|<=gamma_n.                             (3.3)
```

Rearrange the exact affine identity (1.2):

```text
h_i(p^n)-r_i^n
  =[g_i(r^n,p^n)-g_i(h(p^n),p^n)]/c_i(p^n).          (3.4)
```

Use (3.3), Lemma 2.1, and `c_i(p^n)->1` to obtain (3.1).  Divide (1.1) by
the positive absorption probability to obtain (3.2).  QED.

### Corollary 3.2 (the residual forces the fixed-rho side)

For the packet produced from a terminal exploitability witness, at least one
`e_i` is strictly positive.  More quantitatively, the checked theorem

```text
QuittingTerminalExploitabilityWitness.
  exists_pos_uniform_normalizedSingletonPacketDefect
```

in `SingletonPacket/Defect.lean` supplies `delta>0` such that

```text
delta <= max_i mu_i e_i <= max_i e_i.                (3.5)
```

Hence the actual constrained-root subsequence cannot enter the Simon
normalized-motion producer for any error sequence tending to zero.

After the exported Proposition 44 is formalized, the counterexample
assumption itself excludes both the instant and the stationarily generated
branches.  Its contrapositive then supplies one `rho in (0,1)` such that every
`rho`-rational support-local `rho` row satisfies the fixed lower bound.
The roots above meet that fixed-scale interface after the exact repair in the
next paragraph, so they realize the failure alternative rather than
contradicting it.

## 4. Exact endpoint repair and the quantitative fixed-rho statement

For large `n`, define

```text
r_i^n=h_i(p^n)+g_i(h(p^n),p^n)/c_i(p^n).             (4.1)
```

Then (1.2) gives

```text
g_i(r^n,p^n)=0                                       (4.2)
```

for every player.  Thus `p^n` is exactly support-local at `r^n`.  Moreover

```text
r_i^n -> z_i-e_i=s_i.                                (4.3)
```

Punishment normality says `chi_i<=s_i`; therefore, for every fixed `rho>0`,
these tails are eventually `rho`-rational.  Equations (1.1) and (4.1) give

```text
||f(r^n,p^n)-r^n||_infinity/q(p^n)
  =max_i [-g_i(h(p^n),p^n)/c_i(p^n)]
  ->max_i e_i.                                       (4.4)
```

Consequently Simon's fixed-`rho` lower bound implies only

```text
rho<=max_i e_i.                                      (4.5)
```

This is compatible with (3.5).  It yields neither a terminal-gap
contradiction nor a rank decrease.  Re-deriving a positive packet-defect floor
from (4.5) would be weaker than the already checked compact packet-defect
theorem and is not a new consumer.

## 5. Exact residual-compatible falsifier

The necessity of the surplus obstruction can be tested without assuming a
counterexample game.  Let `I=Fin 4` and use the checked paired-singleton matrix

```text
M = [[ 0, 3,-1,-1],
     [ 3, 0,-1,-1],
     [-1,-1, 0, 3],
     [-1,-1, 3, 0]].                                  (5.1)
```

Define a quitting table by

```text
reward({j})_i=M_ij,
reward(S)_i=0 when |S|>=2.                            (5.2)
```

Every row of `M` sums to one and its diagonal is zero.  Therefore uniform
mass `mu_j=1/4` and target zero form a full-support normalized singleton
packet with

```text
e_i=1/4                                               (5.3)
```

for every player.  The normalized singleton matrix is exactly `M`; the named
checked matrix theorems in the paired-singleton example give full normal core,
standard `Q`, no homogeneous simplex solution, and failure of projective
`Q`-bar.  Thus (5.2) realizes all static `ResidualHardClass` fields.  Also
`chi_i<=max(reward({i})_i,0)=0`, so every player is punishment-normal.

This table deliberately has no terminal exploitability witness: all four
players Quitting surely at date zero is an exact terminal Nash profile.  A
unilateral Continue deviation leaves three sure quitters, and both resulting
coalitions have payoff zero.  Thus the example is residual-compatible, not a
counterexample to the conjecture.

Let every player use marginal Quit probability `t in (0,1)`.  Put

```text
q(t)=1-(1-t)^4,
h_i(t)=t(1-t)^3/q(t),
c_i(t)=(1-t)^3.                                      (5.4)
```

Collisions pay zero and every matrix row sums to one, so these formulas are
exact.  Forced Quit pays zero.  Forced Continue has current absorbing
contribution `t(1-t)^2` and continuation contribution `c_i(t)h_i(t)`.  Hence

```text
g_i(h(t),p(t))=-t(1-t)^2-(1-t)^3 h_i(t)<0.           (5.5)
```

The exact endpoint-repaired tail is

```text
r_i(t)=h_i(t)+g_i(h(t),p(t))/c_i(t)
      =-t/(1-t).                                     (5.6)
```

At this tail every endpoint difference is zero, while

```text
||f(r(t),p(t))-r(t)||_infinity/q(t)
  =h_i(t)+t/(1-t) -> 1/4.                            (5.7)
```

For every `gamma>0`, choosing `t/(1-t)<=gamma` makes (5.6)
`gamma`-rational because `chi_i<=0`.  Nevertheless, for all sufficiently
small `t`, the normalized motion in (5.7) is greater than `1/8`.  Thus even
exact support optimality, rationality, a vanishing fully mixed root family,
full normal core, and the complete hard LCP screen do not force Simon's
small-motion hypothesis.  The terminal witness is indispensable, and when it
is restored it strengthens the obstruction through (3.5) rather than
removing it.

## 6. Conjecture-facing disposition and pivot

The Simon route does not consume the current Fin4 constrained-root source.
The precise failed implication is

```text
vanishing full-support stationary roots with endpoint signs
  -> support-local tails with vanishing normalized motion.
```

Proposition 3.1 proves the opposite on the actual compact-limit subsequence:
the normalized motion converges to the nonzero packet surplus.

The best current note-mined replacement has an explicit arrow.  Sections
1--9 of
`CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT.md`, reviewed
by `CODEX_RAMSEY`, prove that every quantitative Fin4 hard residual and every
prescribed singleton owner yield one actual singleton-base stationary source
with:

* exactly one positive debt coordinate, at the prescribed owner;
* three free coordinates solved against unrestricted behavioral deviations;
* a strict-superset atom of fixed positive mass;
* a source-matched paid first-disagreement row;
* a distinct zero-debt reset owner with unit incidence; and
* the same semantic pair and complete law accepted by
  `exists_fixedLawResetDispatch`.

That result has a named actual source and a checked downstream consumer.  Its
remaining obstruction is exactly the reset dispatcher's all-Continue arm; it
does not claim a payoff near-return or the full conjecture.  The unreviewed
Section 10 solo-carrier descent is a separate delta and should not be bundled
into the reviewed handoff.

## 7. Source audit and nonclaims

Declarations inspected for this note:

```text
NormalTerminalGapConstrainedStationary.lean
  exists_quantitative_normalTerminalGap_root
  exists_fullSupport_normalizedSingletonSourcePacket_of_normal_terminalGap

NormalTerminalGapFullSupportCompactLimit.lean
  exists_fullSupport_normalizedSingletonSourcePacket_of_vanishingRoots
  abs_quittingRootEndpointDifference_add_singletonLCPResidual_le

SingletonPacket/Surplus.lean
  exists_active_strictSingletonSurplus

SingletonPacket/Defect.lean
  exists_pos_uniform_normalizedSingletonPacketDefect

FourPlayerPairedSingletonLCP.lean
  pairedSingletonMatrix_normalCore_eq_univ
  pairedSingletonMatrix_standardQ
  pairedSingletonMatrix_noHomogeneous

FourPlayerPairedSingletonResidualHard.lean
  pairedSingletonMatrix_not_projectiveQBar
  residualHardClass_of_normalizedSoloMatrix_eq
```

The last residual-hard adapter is private in the checked example file; only
its mathematical argument, not the private declaration, is invoked for the
new table (5.2).

No Lean theorem is claimed for Propositions 3.1 or the zero-collision
completion.  No fixed-rho result is claimed until the exported Simon theorem
is formalized.  This note does not produce a uniform payoff, contradict the
terminal witness, decrease a well-founded rank, or improve the already
checked packet-defect constant.
