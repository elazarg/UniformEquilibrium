# Independent audit of the square-root clock-rigidity packet

Reviewer: `CODEX_CEDAR`

Reviewed files (read-only external inputs):

- `../infinite/INCENTIVE_GADGET_BREAKTHROUGH.md`;
- `../infinite/PAIR_CLOCK_RIGIDITY_COMPILER.md`;
- `../infinite/TWO_GATE_STRATEGIC_REDUCTION.md`.

Maintained question: `questions/INCENTIVE_GADGET.md`.

Existing conference comparison:
`notes/CODEX_CEDAR__INDEPENDENT_CLOCK_TOGGLE_GADGET.md`,
`notes/CODEX_CEDAR__KILOBLOCK_SIMULTANEOUS_HAZARD_PURIFICATION.md`,
and Propositions 17--18 of
`notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md` with Noether's Round 4
review.

## Verdict

**REVISE, then seek a second independent review.**  The exact local and
global identities, equality classification, quantitative constants, and
finite two-gate deviation formulas are valid ordinary mathematics.  The
source-matched counterfactual theorem also appears valid, but the displayed
proof does not yet prove its player-deleted assertion: prescribed-law
outside absorption is not automatically opponent-only outside absorption.
There is a short repair using a common-clock coupling and the uniform lower
bound on survival through the first gate.  That repair should be written into
the theorem before promotion.

The packet is genuinely stronger than the already reviewed inequality
`ell^2 >= 4ab`.  Its new content is the exact nonnegative slack ledger,
complete positive-mass equality classification, quantitative near-equality
rigidity, and reduction of the sharp boundary to two one-parameter
all-behavior gate tests.  It does **not** construct the reward-table producer
asked for by `INCENTIVE_GADGET`, and it does not refute that producer.

## 1. Probability mode and exact identities

The intended probability mode is the project's ordinary behavioral one.
Before absorption the only public history is the deterministic all-Continue
word, so each player's planned Quit time depends only on that player's private
coins and the date.  The planned times are independent across players.  No
public correlation is being used.

With `z_t=sqrt(S_t)` and the displayed abbreviations `u,v,r,s,h`, direct
expansion gives

```text
(x_t+y_t+z_(t+1))/z_t = h (v r + u s + u r).
```

The inequalities `u+v<=1` and `r+s<=1` imply

```text
v r + u s + u r = r(u+v)+us <= r+us <= r+s <=1.
```

Both claimed local ledgers expand exactly to

```text
e_t/z_t = 1-h(ur+vr+us).
```

Thus every term in (2.1) and (2.2) is nonnegative.  The formulas include
arbitrary atoms, simultaneous quitting, additional players, and Never mass.

Since `a=sum x_t^2` and `b=sum y_t^2`, telescoping gives

```text
X+Y+E+z_infinity=1,
Delta=z_infinity+E+(X-sqrt(a))+(Y-sqrt(b)),
```

and rationalizing the final two differences gives (3.2).  Formula (3.4)
also checks:

```text
ell-2 sqrt(ab)
 = 1-(sqrt(a)+sqrt(b))^2
 = Delta (1+sqrt(a)+sqrt(b)).
```

This recovers the known `ell^2>=4ab` inequality, but the decomposition itself
is new relative to the reviewed Cedar/Gauss proofs I found.

## 2. Equality classification

The local classification is exact when the qualifier “positive target
amplitude” means `x_t+y_t>0`.  For example, if `x_t>0`, equality in (2.1)
forces `h=1`, `r+s=1`, `u+v=1`, and `s(1-u)=0`.  Since `x_t>0` gives `v>0`
and hence `u<1`, one obtains `s=0`, `r=1`, and equality in the two-coordinate
Cauchy inequality gives `q_1=q_2`.  Thus only pair `A` is active.  The `B`
case is symmetric.  Both target amplitudes cannot be positive at one
zero-defect root.

Globally, equality with `a,b>0` forces `Delta=0`.  Then `z_infinity=E=0`,
and

```text
X^2-a=2 sum_(s<t) x_s x_t=0,
Y^2-b=2 sum_(s<t) y_s y_t=0.
```

There is exactly one positive `x` date and one positive `y` date.  At a
zero-defect date with neither amplitude positive, the same ledger forces the
all-Continue root.  Therefore the later selected gate must be sure: if its
hazard were below one, positive survival would remain forever, contradicting
`z_infinity=0`.  The two displayed chronological orientations and
`(a,b,ell)=(p^2,(1-p)^2,2p(1-p))` follow.

In `PAIR_CLOCK_RIGIDITY_COMPILER.md`, “exactly one of the alternatives” is
best replaced by “one alternative holds on the selected subsequence.”  A
single original sequence may alternate the two orientations and therefore
have subsequences of both types; the classification of each chosen
subsequence is still exclusive.

## 3. Quantitative constants

The scale-free concentration estimate is correct.  If `m_A=max x_t`, then

```text
X-m_A <= (X^2-a)/X
       = (X-sqrt(a))(X+sqrt(a))/X
       <= 2 Delta,
```

and similarly for `Y`.  The maximum exists for a positive summable sequence.
Also `E<=Delta` and `z_infinity<=Delta`, so Never mass is at most
`Delta^2`.

Assume `t_A<t_B`.  Before `t_A`, both amplitude sums omit their respective
maxima; hence

```text
1-z_(t_A) <= 2 Delta + 2 Delta + Delta = 5 Delta.
```

Thus absorption before `t_A` is
`1-z_(t_A)^2 <= 2(1-z_(t_A)) <=10 Delta`.  The identical telescope on the
strict interval `(t_A,t_B)` proves the second `10 Delta` bound.  After
`t_B`,

```text
z_(t_B+1)
 <= z_infinity + sum_(t>t_B)x_t + sum_(t>t_B)y_t + E
 <= Delta+2Delta+2Delta+Delta=6Delta.
```

Finally

```text
y_(t_B) >= Y-2Delta >= sqrt(alpha)-2Delta.
```

Since `y_(t_B)<=z_(t_B)`, the conditional all-Continue probability at the
later row is at most the square of
`6Delta/(sqrt(alpha)-2Delta)`.  Equivalently, unconditional survival after
that row is at most `36 Delta^2`.  The constants `10,10,6,36` are therefore
correct; the source notes should include these short telescopes instead of
only referring to them.

## 4. Source-matched counterfactual repair

The current proof ends with the sentence that outside the selected dates the
“total opponent absorption probability tends to zero.”  That conclusion does
not follow literally from prescribed-law outside absorption: deleting one
player's clock can expose a later opponent event which that player's original
clock preempted.

Here the desired conclusion is nevertheless repairable.  Couple the original
profile and the unilateral pure-time deviation using the same opponent
clocks.  Before the first selected date, any newly exposed history must lie
under an original pre-first-date absorption event, whose probability is
`O(Delta_n)`.  At the first gate, if the deviator is an `A` member, removing
its Quit hazard increases reach of the strict middle interval by at most

```text
1/(1-q_(t_n,i)) -> 1/(1-p) <= 1/sqrt(alpha).
```

For every other player that reach ratio tends to one.  The prescribed strict
middle absorption is `O(Delta_n)`, so the player-deleted middle absorption is
still `o(1)`.  At the later gate, either the deviator is outside `B` and the
two `B` opponents quit surely in the limit, or the deviator is a `B` member
and the other `B` member does.  Survival beyond the gate is therefore `o(1)`
for every one-player deviation.  Quit at either selected date terminates the
remaining exceptional branches immediately.  Coordinatewise convergence of
the two selected roots then identifies every terminal coalition law.

This coupling proves convergence for Quit at `t_n`, Quit at `s_n`, and Never,
uniformly for each fixed player.  Bounded rewards convert total-variation
convergence into payoff convergence.  The repaired proof should be stated,
not left implicit, because deleted-clock control is a recurring false
inference elsewhere in this project.

## 5. Two-gate strategic reduction

All displayed values in `TWO_GATE_STRATEGIC_REDUCTION.md` check.

- A gate player has exactly the listed Quit-0, Quit-1, and Never laws.
- A backup player's prescribed Quit-1 value is `U_i`; Quit-0 and Never give
  the displayed four-outcome mixtures.
- An outsider's prescribed Never value is `U_i`; Quit-0 and Quit-1 give the
  displayed joins.
- Against the fixed opponents, absorption occurs by date one.  Every
  deterministic Quit time is therefore equivalent to Quit 0, Quit 1, or
  Never.

The checked declaration
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean` then
upgrades this finite list to unrestricted unilateral behavioral deviations.
The terminal-gap consumer is
`not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap` in
`UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.

One notation repair is needed: the setup allows an arbitrary finite set of
additional players, so the exploitability maximum should be `max_{i in I}`.
The hard-coded `max_{1<=i<=6}` is correct only after explicitly specializing
to the proposed six-player table.

With the repaired counterfactual lemma, Corollaries 2/7.1 and 3 are valid.  A
vanishing-exploitability sequence at sharp clock slack yields a literal gate
with zero exploitability, and a uniform positive lower bound for both gate
functions excludes that sequence.

## 6. Novelty and maintained-question boundary

Already known and independently reviewed:

- `sqrt(a)+sqrt(b)<=1`, `ell>=2sqrt(ab)`, and `ell^2>=4ab` for arbitrary
  independent countable clocks;
- the many-disjoint-pair version; and
- unrestricted behavioral best-response reduction to deterministic Quit
  times.

Genuinely new in the submitted packet:

- the exact local/global nonnegative defect identity;
- the complete equality classification for `a,b>0`;
- the quantitative concentration and survival constants; and
- the source-matched reduction of the saturated arbitrary-clock boundary to
  two finite one-parameter strategic tests.

The multi-coalition Section 8 is not needed for this advance.  The equal-pair
case overlaps the reviewed Gauss result, while the broader unequal-size
form has no present strategic consumer.  It should be omitted from any first
export packet.

The result narrows only the **sharp-saturation branch**.  It supplies neither
a rational reward table nor an actual-data argument that low exploitability
forces `a,b>=alpha` and `Delta->0`.  In particular it is not an answer to the
positive or negative alternatives in `INCENTIVE_GADGET` by itself, and the
clock scripts are regressions rather than proofs.

## 7. Export recommendation

After the two bounded repairs above, this is a plausible strict-reduction
export candidate, limited to the two-pair ledger, equality/stability theorem,
source-matched rigidity, and finite strategic consumer.  The packet would
need to say explicitly that its actual-data adapter starts only from an
already near-saturated clock sequence and that the reward producer remains
open.  Because the claimed reduction covers arbitrary behavioral profiles
and unrestricted unilateral deviations, `exports/README.md` requires a
second independent falsification review before promotion.  I do not recommend
placing the current proof-sketch version in `exports/` yet.

