# Independent falsification of the quitter-only and target-lock results

Reviewer: `CODEX_EULER`

Source reviewed:
[`INCENTIVE_GADGET_BREAKTHROUGH_QUITTER_ONLY_AND_TARGET_LOCK.md`](../../INCENTIVE_GADGET_BREAKTHROUGH_QUITTER_ONLY_AND_TARGET_LOCK.md)

Verdict: **mathematical PASS, with four bounded statement-definition repairs**.
The six-player producer, robust constants, target-lock theorem, participant-
only all-behavior theorem, and `2 delta` perturbation estimate are correct.

## Six-player producer and robust completion

For each outsider `d`, Never gives zero in the integer table and prescribed
payoff is exactly `-31 Pr(A union {d} subset F)`, giving (3.5).  Every strict
superset of `A` contains one of the four outsiders, so the union bound gives
`c<=4g/31`.  Each target member can secure one by Quit-now, while

```text
u_1+u_2=E|F intersect A|=2a+2c+s<=1+a+c.
```

Thus `2-2g<=1+a+4g/31`, exactly yielding `g>=31(1-a)/66` and the displayed
leftover bound.  The numerical substitutions and the consequence from the
checked independent-clock inequality `ell^2>=4ab` are correct.

Under the bounded completion, Never pays an outsider at least `-1`, while
the prescribed payoff is at most `1-32p_d`; hence
`p_d<=(2+epsilon)/32`, `c<=1/4+epsilon/8`, and (4.3)--(4.4) follow.  The
general `m`-member calculation is also correct once its assumptions are made
explicit as requested below.

Section 3 meets the maintained question's partial-producer threshold: from
actual low terminal exploitability it forces one named pair mass and the
leftover bound with fixed rational constants.  It does not force the second
pair mass; indeed (3.10) forces that mass small in this table.

## Target lock and arbitrary behavioral deviations

At the pure `A` row, a target member's only effective deviation is to omit
itself, producing the other member's singleton and payoff zero instead of
one.  An outsider's only effective toggle is to join, producing exactly the
triple `A union {d}` and payoff `-31` instead of `r_d(A)>=-1`.  No unilateral
deviation can produce a coalition of size four or more: all other outsiders
remain Never.  Later history is unreachable because the unchanged target
member(s) quit surely at date zero.  Therefore the membership-toggle test in
`UniformEquilibrium/Quitting/Paths/SureExitSet.lean` controls every randomized
and history-dependent behavioral deviation.  Theorem 5.1 and the general
sure-exit structural corollary are sound.

## Participant-only stationary equilibrium

The one-shot reduction is exact.  Pure Continue always pays zero: absorption
by opponents leaves the player outside the first coalition, and all-Continue
uses the zero Never payoff.  One-shot Nash complementarity therefore gives
the three cases (6.3).

For the stationary repetition, with `rho=product_j(1-q_j)`, the recursion is

```text
V_i=q_i Q_i+rho V_i.
```

If `rho<1`, this gives (6.4).  If no player is sure to Quit, every positive
`q_i` is interior and has `Q_i=0`; inactive players have zero numerator.  If
some player is sure, `rho=0`, and the three complementarity cases give
`V_i=max(0,Q_i)` coordinatewise.  If `rho=1`, every `q_i=0`, every
`Q_i<=0`, and the same identity holds with value zero.

Against the stationary opponents, survival reveals no changing state.
Quitting at any reached date has the same conditional value `Q_i`; continuing
until an opponent quits and Never both pay zero.  Every arbitrary behavioral
stopping rule is therefore bounded by `max(0,Q_i)=V_i`.  This checks the
sure-quitter, no-sure-quitter, and all-Continue boundaries and proves exact
all-behavior terminal Nash, not merely stationary optimality.

For the passive perturbation, participant coordinates are unchanged and an
absent player's terminal reward changes by at most `delta`; Never stays zero.
This holds for the prescribed profile and every unilateral behavioral
deviation, so deviation gain changes by at most `2delta`.  Corollary 7.1 is
correct.

## Required repairs

1. In Corollary 5.2, define the empty-row convention
   `r_i(empty)=0` (the Never payoff) before writing
   `r_i(G\{i})`, or restrict the displayed notation and treat singleton `G`
   separately.  As written, `reward` is defined only on nonempty coalitions.
2. State the hypotheses of (4.7): `G` is nonempty of size `m`, target-member
   rewards retain the participant indicator used in the proof,
   `M,R>=0`, and `M+R>0`.  Otherwise its denominator and target-security step
   are not literally quantified.
3. Define `delta(r)` as the maximum of `0` together with the passive
   magnitudes (or assume there is at least one absent-player coordinate).
   For a one-player game the indexing set in (7.1) is empty, although the
   intended value is zero.
4. In the status summary, qualify “arbitrary bounded completion on every row”
   as an arbitrary completion of the **outsider coordinates** allowed by
   (4.1)--(4.2); the two target coordinates remain fixed by (3.1).

These repairs do not change any proof or constant.

## Source and novelty check

The checked sure-exit membership-toggle theorem directly supports Section 5.
The checked acyclic-solo, signed-influence, and odd-blocker results cover
different structural classes and do not subsume the participant-only theorem.
A narrow source search found no existing declaration asserting stationary
all-behavior equilibrium for every finite participant-only reward table.
Thus Theorem 6.2 is a genuine universal-class no-go at the current ordinary-
mathematics level.
