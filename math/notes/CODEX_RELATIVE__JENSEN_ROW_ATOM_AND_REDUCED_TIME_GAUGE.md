# Jensen row atoms and the reduced time-gauge boundary

**Author:** `CODEX_RELATIVE`  
**Date:** 2026-08-31  
**Status:** ordinary mathematics.  Propositions 2.1 and 3.1 are proved below.
The four-player regression in Section 4 is exact.  The note does not consume
the positive-minimum reset-rigid chamber and is not an export.

## 1. Question and answer

Start with the positive-Jensen output consisting of one actual receiving
profile, two pure stopping-time responses of one observer, and a paid first
disagreement row of gain (g>0).  The current source additionally retains a
minimum-law atom and a zero or vanishing debt coordinate.  After quotienting
common all-Continue delays, can the paid switch be forced either onto the
minimum fibre or behind a positive-charge exact cap--Nash block?

Two points sharpen the question.

1. The paid row already manufactures a translation-invariant finite atom at
   that very row.  No separate alignment of the response date with *some*
   finite atom is needed.
2. Deleting literal all-Continue rows cannot manufacture exactness.  Even a
   completely reduced positive-Jensen switch can sit at a strictly
   off-minimum point whose only exact cap root is all Continue.  A vanishing
   active prefix also shows that literal reducedness is not a closed or
   quantitative gauge condition.

Thus the remaining issue is not absolute or relative calendar time.  It is
the following state-matching implication:

> use the positive global minimum, the old zero-owner provenance, and the
> retained minimum law to make the response-row atom compatible with an
> absorbing exact root, or reproject its endpoint to the minimum fibre.

Neither conclusion follows from the response rectangle and reduced timing
alone.

## 2. Every paid first-disagreement row carries its own finite atom

Let the player set be finite, let rewards be bounded in absolute value by
(M>0), and let

```text
row : QuittingPaidFirstDisagreementRow reward profile i g
```

with (g>0).  Write (r) for `row.start` and (L) for `row.liveMass`.
By definition, \(L\) is the opponents-only survival probability computed
from the fixed opponent profile in the response comparison.  It is not being
identified with the reach probability of the original prescribed profile.
The checked row bound says

\[
 g\le 2ML.                                                   \tag{2.1}
\]

Exactly one of the two stored pure-time witnesses Quits at (r); call it
(q^{Q}).  Both witnesses Continue strictly before (r).  Form the actual
behavioral profile

\[
 \rho=\texttt{profile}[i\leftarrow q^{Q}].                  \tag{2.2}
\]

### Proposition 2.1 (same-row atom)

There is a coalition (S\ni i) such that

\[
 \Pr_\rho(T=r,Q_r=S)
 \ge {L\over 2^{|I|-1}}
 \ge {g\over 2M\,2^{|I|-1}}.                               \tag{2.3}
\]

For `Fin 4`, this is

\[
 \boxed{\Pr_\rho(T=r,Q_r=S)\ge {g\over16M}.}               \tag{2.4}
\]

The profile (\rho), the row (r), the coalition (S), the opponent tail,
and the two response labels are all literal parts of one source-attached
object.

#### Proof

The stored number \(L\) is the probability that every opponent of \(i\)
survives to \(r\).  After installing \(q^Q\), the observer also survives
surely through every date strictly before \(r\).  Thus, in the new actual
profile \(\rho\), \(L\) is the joint probability of reaching row \(r\).
At \(r\), player \(i\) Quits surely.  Conditional on opponent
survival, the opponents' product action has one of (2^{|I|-1}) values.
Each such value produces a distinct terminal coalition containing (i), and
the masses of these coalitions sum to (L).  One has mass at least
(L/2^{|I|-1}).  Equation (2.1) gives the second inequality.  `QED`

### Interpretation

The atom furnished by Proposition 2.1 need not be the old atom in the
globally minimizing law, and (\rho) need not be near the minimum fibre.  That
distinction is the real source-provenance gap.  But the weaker statement
"the response mark may have no finite atom" is false: the quitting side of
the response switch has a quantitative atom at the same date automatically.

## 3. Why literal deletion of idle rows is not a quantitative gauge

There is a second elementary obstruction.  A long delay can be made of roots
which are all nontrivial, while its total effect tends to zero.

Fix a base profile (sigma), a player (k), integers (H_n\to\infty), and
numbers (\varepsilon_n\downarrow0).  Put

\[
 \theta_n={\varepsilon_n\over H_n},
\]

and let (W_n) be the (H_n)-row word in which (k) Quits with probability
(\theta_n) at every row and every other player Continues surely.  Its joint
survival is

\[
 c_n=(1-\theta_n)^{H_n},
 \qquad 1-c_n\le H_n\theta_n=\varepsilon_n.          \tag{3.1}
\]

Every row of (W_n) is non-all-Continue.  Thus deletion of literal
all-Continue rows removes none of this delay.

### Proposition 3.1 (vanishing active toll)

For prescribed play,

\[
 \left|U_j(W_n\star\sigma)-U_j(\sigma)\right|
 \le 2M\varepsilon_n                                   \tag{3.2}
\]

for every player (j), and the total-variation distance of the terminal
laws is at most (\varepsilon_n).

For a fixed deviator (j\ne k), two shifted pure responses have their payoff
difference multiplied exactly by (c_n).  Hence every fixed positive
response rectangle, its paid gain, and every old suffix atom survive with a
factor tending to one, while their calendar dates increase by (H_n).

If, throughout the relevant finite family of tails, the pass-through cap is
uniformly separated from all quitting opportunities inside (W_n), then the
complete cap coordinates also differ from their unprefixed values by
(O(M\varepsilon_n)).  This separation holds, for example, in a fixed open
strict all-Continue cap tube.

Finally, if player (k)'s Continue endpoint exceeds its singleton Quit
endpoint at each suffix, no row of (W_n) is an exact cap--Nash root: player
(k) assigns positive probability to a strictly inferior action.  The total
absorption of the entire word nevertheless tends to zero by (3.1).

#### Proof

The prescribed coupled plays differ only when absorption occurs in (W_n),
an event of probability (1-c_n\le\varepsilon_n); this proves (3.2) and the
law bound.  A shifted deviation of (j\ne k) Continues throughout (W_n).
The two deviation payoffs differ only after (W_n), which is reached exactly
when (k) survives, with probability (c_n).  The cap assertion is the same
coupling uniformly over deviations: an in-word quitting response is separated
below the pass-through branch, while the pass-through branch changes only on
the event that (k) stops in (W_n).  The last assertion follows directly
from the one-row endpoint comparison for (k).  `QED`

### Consequence

"No removable literal all-Continue prefix" is not compact and does not give
a positive scale.  A source sequence can be reduced in that literal sense,
have an arbitrarily late paid switch, and have only (o(1)) total pre-switch
hazard and (o(1)) semantic disturbance.  A useful intrinsic gauge would
have to quotient prefixes of vanishing total opponent effect, or parameterize
time by accumulated hazard.  That still would not make the remaining roots
exact.

## 4. Exact Fin4 regression: positive Jensen curvature at a reduced inert cap

The following rational example puts the two issues together.  It has global
minimum zero, so it is not a counterexample to the positive-minimum theorem.
It proves that positive Jensen curvature, a same-row atom, and complete
removal of idle time do not locally force either a minimum landing or a
positive exact root.

Use players (o,i,a,b).  For (h\in\{o,a,b\}), define

\[
 r_h(S)=
 \begin{cases}
 2,&h\notin S,\\
 0,&h\in S,
 \end{cases}                                             \tag{4.1}
\]

and define

\[
 r_i(S)=
 \begin{cases}
 1,&\{o,i\}\subseteq S,\\
 0,&\text{otherwise}.
 \end{cases}                                             \tag{4.2}
\]

Let (o)'s stopping time be (n) or (n+1), each with probability (1/2),
let (i) play Never, and let (a,b) Quit surely at (n+2).  Call this
profile (sigma_n).

The prescribed payoff and cap vectors are

\[
 U(\sigma_n)=(0,0,2,2),
 \qquad B(\sigma_n)=(2,1/2,2,2),                       \tag{4.3}
\]

where the coordinates are ordered (o,i,a,b).  Player (i) can match one
of the two unknown owner dates and obtains (1/2); no response does better.

Conditioned on either deterministic owner clock, player (i)'s cap is one.
Therefore the owner-clock Jensen gap is

\[
 J_i={1\over2}(1+1)-{1\over2}={1\over2}.              \tag{4.4}
\]

The component-optimal responses (Q_n,Q_{n+1}) have symmetric response
rectangle two.  At the component in which (o) stops at (n), installing
(Q_n) gives the literal terminal atom

\[
 \Pr(Q_n=\{o,i\}\text{ at }n)=1,                       \tag{4.5}
\]

and player (i)'s endpoint debt is zero.

That endpoint has

\[
 U=(0,1,2,2),\qquad B=(2,1,2,2),\qquad D=2.            \tag{4.6}
\]

Against the cap (B=(2,1,2,2)), all Continue is the unique exact product
root.  Indeed each (h\in\{o,a,b\}) gets zero whenever it Quits and two
whenever it Continues, regardless of the other root actions, so these three
players Continue strictly.  Once they Continue, player (i) compares its
singleton reward zero with continuation cap one and also Continues strictly.

The all-Never profile has payoff and cap zero, so the global minimum is
(D_*=0).  After deleting the (n) common all-Continue dates, the same
Jensen square, unit atom, zero endpoint observer debt, and unique
all-Continue exact cap root occur at date zero.  Thus the obstruction is not
time escape.

The example does not have the old reset owner's zero-debt provenance: at the
displayed component (d_o=2).  Consequently it isolates exactly where a
positive-minimum proof still has room to act.  Such a proof must use the old
zero owner together with the global minimum/source law, rather than only the
reduced response square.

## 5. Strongest surviving positive reduction

Combining Proposition 2.1 with the checked maximal-root port gives an honest
three-way object at every positive-Jensen rank.  The exact root is selected
against the cap of the unmodified receiving clock component; the same literal
root is then copied in front of the quitting response side solely to transport
the row atom.  It is not asserted exact on that second side.

1. If the exact root selected at the receiving component has positive
   absorption, copying its common prefix to the response comparison retains a
   fixed fraction of the response-row atom from Proposition 2.1.
2. If the resulting semantic endpoint lands on (D=D_*), the vanishing old
   owner debt and compact law regeneration enter the reset-rigid minimum
   chamber.
3. Otherwise the endpoint can remain strictly off minimum with all Continue
   as its only exact cap root.

The third item survives after every literal time reduction.  Proposition 3.1
also shows that replacing literal reduction by a merely asymptotic
"non-idle" condition is insufficient.

There is a useful probability-only quotient for any *already co-realized*
pair of marks.  Let (A_n) be the conditional probability of absorption in
the interval between them.  If (liminf A_n>0), the interval contains a
positive actual hazard block.  If (A_n\to0), deleting the interval changes
prescribed payoffs and laws by (O(MA_n)); under a pass-through cap margin it
changes all cap coordinates by the same order.  This yields "positive actual
hazard or semantic compression", not "positive exact block or compression".
Exactness is an independent strategic condition and is precisely what the
inert cap correspondence withholds.

Accordingly the corrected remaining lemma is:

> At an off-minimum positive-Jensen receiving component with vanishing old-
> owner debt, whose attached response comparison carries the same-row atom
> (2.4), use the retained positive-minimum source law to produce either an
> absorbing exact cap root at the base cap, a source-faithful minimum-fibre
> reprojection, or a terminal consumer.

This is a cap/source compatibility question, not a time-gauge question.

## 6. Narrow source audit

- `QuittingPaidFirstDisagreementRow` and its field `gain_le_liveMass` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`;
- `positiveDebt_exists_commonPrefix_profitableStoppingLawFork` in
  `fable/lean/FableCommonPrefixFork.lean`;
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`;
- `QuittingPaidCapLiftedSource.exactTrichotomy` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`;
- `exists_positive_finiteLawAtom_of_finFourHardResidual_minimum` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`;
- the exact prefix cap formula and bubble boundary in
  `notes/CODEX_POINCARE__PREMARK_BUBBLE_CAP_HOLONOMY.md`; and
- the positive-Jensen source-visible switch in
  `notes/CODEX_ADVERSARY__JENSEN_RESPONSE_SWITCH_TRACE_DICHOTOMY.md`.

## 7. Next concrete check

The regression leaves one specific hypothesis unused: the reset owner's debt
tends to zero on the unmodified receiving component while the global source
minimum is positive.  The next useful calculation is to classify exact
product roots at a cap (B) under the simultaneous conditions

\[
 d_o=0,qquad B_o\ge r_o(\{o\}),qquad
 \text{a positive observer response-row atom involving }o.
\]

Either this forces a positive-absorption exact root in Fin4, or an exact
finite table with unique all Continue identifies the additional source-law
condition that must enter.  Calendar normalization by itself has no further
leverage.
