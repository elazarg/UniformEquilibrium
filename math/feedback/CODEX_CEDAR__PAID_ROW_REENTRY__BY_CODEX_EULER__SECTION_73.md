# Review of Proposition 73 by CODEX_EULER

## Claim reviewed

I independently checked Section 73 of
`notes/CODEX_CEDAR__PAID_ROW_REENTRY.md`.  The proposition starts from a
terminal-semantic carrier point `X^0=(U^0,B^0)` above the punishment floor,
a positive minimum total semantic debt `D_*`, and one singleton gap

```text
U^0_g <= r({g})_g-Delta.
```

It repeatedly chooses an arbitrary exact product root at the currently
reached prescribed coordinate and applies the literal semantic prefix map.
The claimed conclusion is that a uniformly bounded number of rows forces
either a fixed `g`-payoff excursion or a charged row with a quantitatively
interior active player `k != g`.

## Verdict

**PASS as ordinary mathematics.**  The constants, exact source matching,
punishment-floor propagation, semantic-debt descent, and finite telescope all
check.  The result is a genuine well-founded reduction of the persistent
singleton-gap/collision arm.  It is not a payoff-return producer, and neither
of its two terminal alternatives is compiled by the proposition.

Two proof-writing details should be explicit in any promoted version:

1. derive `1 < n` from the positive terminal-exploitability witness before
   dividing by `n-1` in Proposition 53; and
2. in the excursion arm choose the **first** time at which
   `U^t_g > r({g})_g-delta` (unless the crossed alternative already occurred).
   This is what justifies that every preceding row still has the fixed
   singleton gap and hence charge at least `c`.

These are clarifications, not repairs to the mathematical statement in its
maintained terminal-gap context.

## Exact audit

Let `delta=Delta/2` and

```text
c     = delta/(delta+2M),
d     = gamma/(4M),
omega = d^(n-1),
a     = delta*omega,
b     = c*a/(8M).
```

All are positive.  The positive terminal gap forces `M>0`; Proposition 51
also gives `gamma <= 4M`, hence `0 < d <= 1`.  The terminal-gap witness gives
`1<n` through `QuittingTerminalExploitabilityWitness.one_lt_card`, so
`n-1>0`.  Thus `omega,a,b>0`, and Archimedean choice supplies an `N>=1` with
`N*D_* * b > E_0`.

At a reached carrier pair `X^t`, finite mixed Nash supplies an exact product
root `q_t` against `U^t`.  Setting

```text
X^(t+1)=quittingTerminalSemanticPrefix reward q_t X^t
```

is the correct orientation.  The declaration
`quittingTerminalSemanticPrefix_mem_carrier` preserves the compact attainable
semantic carrier.  Its first coordinate is
`quittingRootSuccessorPayoff reward U^t q_t`.  The checked floor inequality
`quittingPunishmentValue_le_rootSuccessorPayoff_of_tail_ge` therefore
propagates `U^t>=P` to `U^(t+1)>=P`.  Carrier membership also supplies the
canonical reward-box bound needed to package any finite initial segment as a
`QuittingPunishmentFloorFinitePrefix`.

As long as

```text
U^t_g <= r({g})_g-delta,
```

Propositions 50--53 apply with constants independent of `t`.  Every selected
root has absorption at least `c`, every marginal is at most `1-d`, and
Proposition 53 gives exactly the exhaustive split

```text
q_t(g) < c/2 and some k!=g has c/(2(n-1)) < q_t(k) <= 1-d,
```

or an actual collision event of probability at least

```text
(c/2)*(a/(4M)) = c*a/(8M) = b.
```

The adverse joining sign identifies the event but is not needed after this
probability estimate: the full collision mass is at least the event mass.

For the literal finite prefix, the checked declaration
`QuittingPunishmentFloorFinitePrefix.collisionMass_mul_debtSum_le_debtDrop`
states rowwise

```text
collisionMass(q_t)*D(X^t) <= D(X^t)-D(X^(t+1)).
```

Every `X^t` remains in the semantic carrier, so minimum-debt optimality gives
`D(X^t)>=D_*`.  On the noncrossed arm, `collisionMass(q_t)>=b`, hence

```text
D(X^(t+1)) <= D(X^t)-D_* b.
```

Summing `N` such inequalities yields

```text
D(X^N) <= D(X^0)-N D_* b < D_*,
```

contradicting carrier minimality.  This establishes the finite alternative
uniformly over all choices of exact roots.

For the payoff conclusion, take the first threshold-crossing time `t`.  Then
`1<=t<=N`, every preceding root has absorption at least `c`, and

```text
U^t_g-U^0_g
  > (r({g})_g-delta)-(r({g})_g-2delta)
  = delta.
```

If a crossed row occurred earlier, the second alternative already holds.

## Scope

- The argument is semantic-carrier exact: it uses the actual prefix action on
  a carrier point.  A carrier point may be a compactified limit rather than a
  single profile, so “actual” should not be read as asserting an attained
  behavioral profile unless attainability is separately supplied.
- The active `k` is distinct from `g` and quantitatively bounded away from
  both zero and one.  The proposition does not say that `g` remains active.
  It proves outside-face activation only when the maintained owner face is
  the singleton `{g}`; for a larger face, incidence data are still missing.
- The well-founded quantity is `D-D_*` only while the fixed singleton gap
  persists and the crossed alternative is absent.  The proposition does not
  orient or repay the resulting payoff excursion and does not create a
  payoff-near-return, exact connector cycle, or uniform-equilibrium payoff.

## Addendum: Corollary 73A

I separately checked the recurrent-charge consumer added after the main
review.  **Corollary 73A passes.**

Fix an infinite exact floor-safe extension and suppose the set

```text
J={t : c_0 <= absorption(q_t)}
```

is infinite for one `c_0>0`.  The vectors `U^t`, `t in J`, lie in the compact
canonical payoff box.  Total boundedness (or a finite `eta`-cover and
pigeonhole) gives two distinct indices `s<t` in `J` with

```text
|U^t_i-U^s_i|<=eta
```

for every coordinate.  The actual segment with values
`U^s,U^(s+1),...,U^t` and roots `q_s,...,q_(t-1)` is nonempty, exact,
punishment-floor admissible, and begins with the edge `q_s`, whose charge is
at least `c_0`.  Thus it has exactly the orientation and endpoint projection
required by `QuittingPositiveAdmissiblePayoffNearReturnFamily`; recurrence of
caps, debts, roots, or full semantic pairs is not used.

The contrapositive is also exact.  If the maintained varying-edge family is
absent, then on every infinite exact extension `absorption(q_t)->0`: otherwise
some positive threshold is met infinitely often.  If

```text
U^t_g <= r({g})_g-delta
```

held infinitely often, Proposition 50 would give
`absorption(q_t)>=c` at all those indices, contradicting convergence to zero.
Hence eventually

```text
U^t_g>r({g})_g-delta
```

and the initial gap `U^0_g<=r({g})_g-2delta` gives
`U^t_g-U^0_g>delta`.

The scope is correctly limited: this compiles recurrent fixed charge, but it
does not stop a one-way payoff escape followed by diffuse rows whose charges
tend to zero.

## Addendum: Corollary 73B

I also checked the finite-atom endpoint of the one-way escape.
**Corollary 73B passes at its stated semantic-closure scope.**

Under absence of the near-return family, Corollary 73A gives
`absorption(q_t)->0`.  Each marginal Quit probability is bounded above by
joint absorption, so `q_t` converges coordinatewise to the all-Continue root.
Compactness of the terminal-semantic carrier selects a strict subsequence
`X^(t_j)->X^infinity`; the paired roots on that same subsequence converge to
all-Continue.  Closedness of the exact endpoint-Nash inequalities therefore
makes all-Continue exact at `U^infinity`.

The eventual strict excursion only becomes weak after taking the limit, as
stated:

```text
U^infinity_g-U^0_g >= delta.
```

For every exact semantic prefix, the checked collision inequality has a
nonnegative left side, hence total debt is nonincreasing.  Continuity and
global carrier minimality give

```text
D_* <= D(X^infinity) <= D(X^0).
```

Nonnegative coordinate debts then select `i` with
`d_i(X^infinity)>=D_*/n`.  The checked declaration
`exists_terminalOutcomeReward_ge_terminalSemanticEnvelope` supplies a Never
or terminal-coalition outcome `A` with

```text
B^infinity_i <= reward_i(A),
```

which yields the displayed `D_*/n` premium over `U^infinity_i`.  The case
`A={i}` is impossible because exact all-Continue Nash gives
`reward_i({i})<=U^infinity_i`.  Thus a nonempty `A` is either a singleton of
a distinct owner or a coalition of cardinality at least two.

The stated limitations are essential and correct: carrier membership need
not mean one profile attains `X^infinity`; the maximizing atom need not have
positive probability in a realizing approximation; and its pure insertion
is not thereby an exact floor root.  A distinct singleton owner is outside
a separated owner face only with the additional incidence hypothesis noted
in the corollary.

## Addendum: Corollary 73C

The behavioral positive-mass realization also passes.  Put `e=D_*/n>0`.
Sequential density of attainable semantic pairs gives actual profiles
`sigma_j` with both prescribed payoff and unrestricted cap converging to
`X^infinity`.  For large `j`,

```text
B_i(sigma_j)>=B^infinity_i-e/8.
```

The checked pure-time extremality equality for quitting best responses lets
one choose an `Option Nat` pure time (including Never) whose payoff is within
`e/8` of this cap.  Updating only player `i` preserves every opponent's
behavior literally.  Since `B^infinity_i>=U^infinity_i+e`, the deviated
profile `tau_j` satisfies

```text
payoff_i(tau_j)>=U^infinity_i+3e/4.
```

For the fixed high-reward set

```text
H={A : reward_i(A)>=U^infinity_i+e/2},
```

let `p_j=Pr_tau_j(H)`.  Rewards on `H` are at most `M`, and rewards off `H`
are at most the threshold.  Therefore

```text
e/4 <= p_j*(M-(U^infinity_i+e/2)) <= 2M p_j,
```

where the last bound uses `U^infinity_i>=-M`.  Hence
`p_j>=e/(8M)`.  The terminal outcome space has exactly
`1+(2^n-1)=K=2^n` elements, so one high outcome has mass at least
`e/(8MK)`; finite pigeonhole freezes it along a subsequence.  Further source
payoff convergence gives

```text
payoff_i(tau_j)-payoff_i(sigma_j)>=e/2.
```

The same all-Continue Nash inequality excludes the frozen outcome `{i}`.
Thus the gain, fixed terminal mass, and fixed terminal orientation occur on
one source-matched unilateral replacement with opponents unchanged.

The conclusion remains behavioral rather than Bellman: neither the pure-time
replacement nor its terminal mass is an exact simultaneous floor-root charge.
