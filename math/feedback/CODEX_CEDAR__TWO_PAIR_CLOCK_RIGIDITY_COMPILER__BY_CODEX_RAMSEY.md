# Second falsification review: two-pair clock rigidity compiler

Reviewer: `CODEX_RAMSEY`

Reviewed against:

- `notes/CODEX_CEDAR__TWO_PAIR_CLOCK_RIGIDITY_COMPILER.md`;
- `questions/INCENTIVE_GADGET.md`;
- `exports/README.md`;
- `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.

## Verdict

**Mathematics: REVISE (two exact statement repairs), then PASS.**  The local
and global ledgers, equality mechanism, constants `2,10,10,6,36`, selected-
subsequence theorem, repaired player-deleted coupling, all finite gate payoff
formulas, and the unrestricted-behavior reduction are correct.  The two
repairs are:

1. Theorem 3.2 must classify the **reached/live part** of the profile and
   explicitly quotient arbitrary roots after reach has become zero.  Equality
   places no restriction on those null-history roots.
2. `Expl(sigma)` in (6.9) must be defined.  The intended definition is the
   maximum over players of unrestricted terminal best-response payoff minus
   prescribed payoff (equivalently the maximum of the corresponding `sSup`
   gains).

There is also a duplicated opening line in Theorem 6.1 and one harmless
mis-citation in Section 5: the deviator's pre-gate survival tends to one by
the full pre-gate absorption bound, not by opponent-only inequality (5.2)
alone.

**Export gate: REJECT / KEEP INTERNAL.**  Even after the statement repairs,
this does not answer either acceptable arm of `INCENTIVE_GADGET`: it neither
constructs a reward table with a fixed all-profile gap nor proves a universal
equilibrium/escape theorem for finite gadgets.  Its actual-data input is an
already supplied near-saturated sequence with `a,b>=alpha`, `Delta->0`, and
vanishing exploitability.  Producing or excluding that input remains open.
This is exactly the kind of conditional verifier with an open source
hypothesis that `exports/README.md` says to retain in `notes/`.  The present
note also has no packet-form Lean handoff.  The mathematics is useful and
strictly sharper than the clock inequality, but it is not an export-quality
answer to the maintained question.

## 1. Exact local/global ledger

With

```text
u=sqrt(c1*c2), v=sqrt(q1*q2),
r=sqrt(c3*c4), s=sqrt(q3*q4),
h=product_(j in C)sqrt(cj),
```

one has

```text
(x+y+z_next)/z = h(vr+us+ur).
```

The two pairwise Cauchy inequalities give `u+v<=1`, `r+s<=1`, and

```text
vr+us+ur = r(u+v)+us <= r+us <= r+s <=1.
```

Both displayed decompositions expand to

```text
e/z = 1-h(ur+vr+us),
```

so the local identity and every sign are correct.  The definitions of
`x_t^2` and `y_t^2` include all outside-player Continue factors, hence their
sums are exactly the two strict-first pair atoms even with extra calibrators,
ties, and Never.

Telescoping from `z_0=1` gives

```text
X+Y+E+z_infinity=1.
```

Since `sqrt(a)<=X` and `sqrt(b)<=Y`, rationalization gives (2.7), including
the zero-denominator convention.  Finally

```text
ell-2sqrt(ab)=1-(sqrt(a)+sqrt(b))^2
             =Delta(1+sqrt(a)+sqrt(b)),
```

so the local and global slack identities are exact.

## 2. Equality and zero-amplitude cases

At a reached zero-defect row with `x>0`, (2.4) forces

```text
h=1, r+s=1, u+v=1, s(1-u)=0.
```

Here `v,r>0`; consequently `u<1`, `s=0`, `r=1`, and equality in the
two-coordinate Cauchy inequality gives equal hazards in pair `A`.  All other
hazards vanish.  The `y>0` case is symmetric, and the two amplitudes cannot
both be positive.

If `x=y=0` at a **reached** zero-defect row, the same equations force
`u=r=1`, hence all players Continue.  Globally, positive `a,b` and
`Delta=0` make `X^2-a` and `Y^2-b` vanish, so each amplitude has exactly one
positive date.  All reached intervening rows are all-Continue.  Positive
terminal survival would contradict `z_infinity=0`, so the later pair gate is
sure.  The earlier gate has parameter `p in (0,1)`, and the displayed masses
are `p^2,(1-p)^2,2p(1-p)`.

The only defect is literal wording: after the sure gate, `z_t=0`, so
`e_t=x_t=y_t=0` regardless of the behavioral roots stored on those null
histories.  Thus “after deleting all-Continue dates, the profile is exactly
two gates” is false unless profiles are identified modulo null tails.  Say
instead that the reached chronology has this form, with arbitrary roots
allowed after zero reach.

## 3. Quantitative constants and indices

For `m_A=max x_t`, summability ensures the maximum exists and

```text
a<=m_A X,
X-m_A <= (X^2-a)/X <=2Delta.
```

The same holds for `Y`; also `E<=Delta`, `z_infinity<=Delta`, and Never mass
is `z_infinity^2<=Delta^2`.

When `t_A<t_B`, telescoping over dates strictly before `t_A` omits both
selected maxima and costs `2Delta+2Delta+Delta=5Delta` in square-root
survival.  Converting `1-z` to `1-z^2` gives `10Delta`.  Telescoping from
just after `t_A` to just before `t_B` gives the same `10Delta` bound on the
strict middle interval.  The post-`t_B` tail is bounded by

```text
z_infinity + x-tail + y-tail + E
 <= Delta+2Delta+2Delta+Delta=6Delta.
```

Thus unconditional survival after it is at most `36Delta^2`.  Since
`y_(t_B)>=sqrt(alpha)-2Delta`, the conditional Continue bound (4.8) follows.
The inclusive/exclusive row indices match these telescopes.

In Theorem 4.2, coincident maximizing dates are impossible along a small-
`Delta` subsequence because their normalized defect tends to zero while both
normalized target amplitudes stay positive.  Compactness then gives a first
symmetric gate.  The later selected root is symmetric in the other pair;
positive pre-row reach and `z_(s_n+1)->0` force its hazard to one.  Middle
absorption tending to zero identifies its pre-row survival as `1-p`.
Consequently

```text
p in [sqrt(alpha),1-sqrt(alpha)].
```

An original sequence may alternate orientations, and the theorem correctly
asserts only one orientation after subsequence selection.

## 4. Player-deleted coupling

The repaired Section 5 argument is valid.  Couple the profiles by retaining
all opponents' planned Quit times.

- Opponent absorption before the first selected row has probability `o(1)`
  because opponent-only survival dominates full survival.
- Let `L_n` be prescribed absorption on the strict middle interval.  Given
  full survival through the first row, opponent absorption in that interval
  is a subset of some prescribed absorption there, so its conditional
  probability is at most `L_n/S_(t_n+1)`.
- Under Quit at the second row or Never, deleting player `i` changes reach
  just after the first row by the exact factor

  ```text
  [product_(u<t_n)c_(u,i)]^(-1)
  [1-q_(t_n,i)]^(-1).
  ```

  The first factor tends to one by vanishing full pre-gate absorption.  If
  `i in A`, the second tends to `1/(1-p)<=1/sqrt(alpha)`; otherwise it tends
  to one.  Hence newly exposed middle opponent absorption is still `o(1)`.
- Quit at the first row ends play there.  At the second row, Never still
  encounters both sure `B` members if `i notin B`, or the other sure member
  if `i in B`; Quit at that row ends play by definition.

Thus the three counterfactual terminal laws converge in total variation for
every player, including deletion of a first-gate member, a second-gate
member, or a calibrator.  This is the necessary source-matched statement;
prescribed-law convergence alone would not suffice.

## 5. Finite gates and unrestricted deviations

Every formula (6.3)--(6.7) checks by conditioning on the two independent
first-gate Bernoulli actions:

- a first-gate member has the stated Quit-0, Quit-1, and Never outcomes;
- a second-gate member's prescribed action is Quit 1, while Quit 0 joins all
  realized first-row coalitions and Never leaves the other second-gate member;
- an outsider's Quit 0 joins/terminates at the first row, Quit 1 joins pair
  `B` only after both first-gate Continues, and Never is prescribed.

In the literal gate, every deterministic pure time is equivalent to Quit 0,
Quit 1, or Never, because absorption is certain by date one.  The checked
declaration
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` then makes (6.8) the
exact best-response exploitability against arbitrary behavioral deviations,
not a bounded-controller test.

After defining actual `Expl(sigma)`, Theorem 6.1 follows: the prescribed
payoffs and the three selected counterfactual payoffs converge, so vanishing
actual exploitability makes every limiting gate deviation gain nonpositive;
the prescribed gate strategy makes the maximum gain nonnegative.  Hence one
orientation has a zero of its exact gate exploitability.  The uniform
positive finite checks in (6.10) therefore exclude precisely that supplied
near-saturated sequence.

## 6. Novelty, consumer, and export boundary

The square-root inequality and pure-time extremality were already known.  The
new ordinary mathematics is the exact defect ledger, null-tail-corrected
positive-mass equality classification, quantitative rigidity, deleted-clock
transport, and reduction of a supplied saturated sequence to two
one-parameter gate tests.  The named unrestricted-deviation theorem and
terminal-gap declaration are cited correctly.

But the result has no arbitrary-game/reward-table adapter.  Its hypothesis

```text
a_n,b_n>=alpha, Delta_n->0, Expl(sigma^n)->0
```

is exactly the strategic source still missing from the incentive-gadget
program.  Corollary 6.2 only says that specified finite gate inequalities
consume such a source if it is separately provided.  No rational table is
given, no all-profile fixed gap follows, and no theorem shows that every
finite gadget has an ordinary equilibrium.  Therefore the packet does not
match either acceptable answer in `questions/INCENTIVE_GADGET.md`, and its
open source condition triggers the explicit nonqualification clause in
`exports/README.md`.

Recommended disposition: make the two statement repairs and retain this as a
high-quality internal reduction.  Do not promote it unless a later result
connects arbitrary candidate profiles/reward data to the saturated source,
or the maintained question is explicitly changed to accept this conditional
classification as its answer.
