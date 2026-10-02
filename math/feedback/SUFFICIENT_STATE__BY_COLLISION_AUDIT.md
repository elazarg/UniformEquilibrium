# Audit of the response-state collision and finite counterfactual hierarchy

## Status

The examples and algebra in `SUFFICIENT_STATE.md`, Sections 1--2, survive
adversarial checks with calendar-dependent behavioral replacements, Never,
simultaneous quitting, and positive reach.  Theorem 1 needs one explicit
qualification: transition congruence contradicts the example only for a state
that also determines prescribed terminal payoff (as required by strategic
completeness).  A constant quotient of the response signature is a trivial
counterexample to the theorem's unqualified last sentence.

`MARKOV_COMPLETE.md`, Sections 1--7, is mathematically correct under its stated
**complete labelled terminal-outcome** semantics.  The result remains correct
when absorption dates are omitted but quitting-coalition labels are retained.
It is not a theorem for terminal reward-vector laws alone.

## 1. The probe identity

For the table

\[
r^\star(S)=\bigl(1,{\bf 1}_{\{2,3\}\subseteq S},0,0\bigr),
\]

replace player 3 by sure Quit at the first stage of the suffix at date \(n\).
Absorption is then certain at that stage.  Player 2 receives one exactly when
player 2 also Quits, irrespective of players 1 and 4 and irrespective of any
additional tie.  Hence

\[
U_2((S_n\sigma)[3\leftarrow Q_3^0])=x_2^n.
\]

This uses the conditional action probability at the canonical all-Continue
history and remains valid for a calendar-dependent source.  It does not rely
on eventual absorption, response attainment, or a stationary deviation.

If suffix transitions are required only at reached histories, the unrestricted
claim that the state determines every \(x_2^n\) should be restricted
accordingly.  This does not affect either displayed counterexample: the
one-step collision has positive reach on both sides, and every history in the
isolated-spike family has reach at least (1-p).

## 2. Equality of the complete current unilateral response signatures

For the two profiles in Section 2, every absorbing coalition that can occur
under the prescribed profile or one unilateral replacement has reward vector

\[
e_1=(1,0,0,0).
\]

Indeed, when player 1 is replaced, every other player is Never.  When a player
other than 1 is replaced, at most one of players 2 and 3 can be active, so the
second reward coordinate cannot become one.  Thus only the dichotomy
``absorption versus Never'' is visible to `LawPay`.

For a replacement strategy \(\tau_i\), let \(\alpha(\tau_i)\) be its eventual
Quit probability along the canonical all-Continue history.  Calendar
dependence changes the distribution of its finite stopping date but not this
number.  In both source profiles the probability of no absorption is

\[
(1-a)(1-\alpha(\tau_i)).
\]

Fresh behavioral randomization is independent across player coordinates, so
this calculation is exact.  Simultaneous quitting with player 1 creates no
additional payoff-vector atom.  Therefore the pointwise equality of all
replacement-indexed `LawPay` laws is valid.

After one all-Continue step, the two prescribed payoff laws differ by \(a\),
and the history has respective reach \(1-a\) and \(1\).  This is a genuine
positive-reach suffix collision.

The precise collision theorem should be stated as follows.  There is no state
map \(\Phi=f\circ\mathfrak R\) that simultaneously:

1. determines prescribed terminal payoff (or the prescribed `LawPay` law);
2. makes the state-level transition relation for the literal one-step
   all-Continue suffix strategically congruent; and
3. realizes its successors by the corresponding literal suffixes.

Equality of \(\mathfrak R(\sigma)\) and \(\mathfrak R(\rho)\) then forces equal
successor states, strategic completeness forces equal successor payoffs, and
the displayed payoff difference contradicts this.  Without item 1, the
sentence ``no state factoring through \(\mathfrak R\) is
transition-congruent'' is false: the constant state factors through
\(\mathfrak R\) and is trivially congruent.

## 3. Behavioral strategies and independent stopping laws

The reduction used in `MARKOV_COMPLETE.md` is exact for the project's quitting
game semantics.  Before absorption there is one public history at each date,
namely the all-Continue history.  Reading a behavioral strategy on those
histories gives a scalar hazard sequence and hence a stopping law on
\(\mathbb N\cup\{\infty\}\).  The game samples the players' behavioral actions
as a product at each history, so latent first-Quit times can be sampled
independently across players.  Conversely, every stopping law is realized by
its conditional hazards.

Relevant checked support is:

- `quittingTerminalPayoff_eq_rootSequence_profileLiveRoot` and
  `quittingProfileLiveRoot_update_eq_rootSequenceUpdate` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`; and
- `StoppingLaw.stoppingLaw_toScalarHazard` in
  `MathUE/Probability/StoppingLawReconstruction.lean`.

The first two certify reduction to the live root sequence, the next theorem
certifies affinity of every unilateral payoff in the stopping law, and the last gives
exact realization of an arbitrary stopping law.  A Lean implementation of the
full law-valued kernel would still need the corresponding joint product-law
and pushforward declarations; the ordinary-mathematics reduction itself is
sound.

This conclusion relies on the project's independent behavioral
randomization.  It would not hold unchanged in a model with a shared
correlation device or a correlated joint private seed.

## 4. Replacement formula and closure order

Formula (3) is the correct coordinate disintegration.  If the replaced player
is already in the pure intervention set, the intervention overwrites the
replacement.  Otherwise, conditioning on its stopping time \(s\) raises the
pure-intervention order by one.  At order \(n-1\), the only raised query fixes
all players and is the universal Dirac law \(\Gamma(t_I)\).  Thus order
\(n-1\) is closed, and order \(n\) contributes no profile-dependent data.

The deterministic lower-order separation is also valid for every
\(0\le k\le n-2\).  Before the selected replacement, any intervention of at
most \(k\) players leaves one of the \(k+1\) blockers at date \(a\), hiding the
different time of \(h\).  After replacing one blocker and intervening on the
remaining \(k\), the outcomes are coalition \(\{h\}\) versus coalition \(I\).
The argument survives omission of terminal dates: those coalition labels are
already distinct.

Accordingly,

\[
k_{\min}=n-1
\]

is correct **within this labelled pure-intervention hierarchy**.  It should
not be read as a lower bound on every possible sufficient-state encoding.

## 5. Recovery of marginal stopping laws

For \(n\ge2\), the decoder in (16)--(17) is exact even when the terminal law
omits the absorption date.  Put one anchor at finite date \(t\), put every
other intervened player at Never, and leave only player \(i\) uncontrolled.
The coalition is exactly \(\{i,a\}\) precisely when \(T_i=t\).  Putting every
other player at Never makes the Never outcome occur precisely when
\(T_i=\infty\).  These events recover every atom of \(\mu_i\).  The product
pushforward formula reconstructs every response kernel from the marginals.

Therefore \(\mathcal K_{n-1}\) and the labelled marginal stopping-law tuple
are losslessly equivalent on actual profiles.  The associated minimality
claim is valid only in the stated sense: any encoding from which the full
labelled \(\mathcal K_{n-1}\) can be recovered must distinguish every marginal
tuple.

If the terminal observation is only the **reward vector**, coalition aliases
can destroy (16), (17), and the deterministic separation.  In particular, the
claim that the separation is independent of the reward table is true for
labelled coalition laws, not for `LawPay` as used in `SUFFICIENT_STATE.md`.
This semantic distinction should remain explicit wherever the two documents
are connected.

## Verdict

The response-state collision is a valid negative result after adding the
strategic-observation hypothesis to Theorem 1.  The finite hierarchy theorem
is a valid and useful exact characterization for labelled terminal outcomes:
order \(n-1\) is the first self-closed pure-intervention order and is
equivalent, on actual profiles, to the complete tuple of independent stopping
laws.  Neither statement provides compact all-depth suffix congruence; rather,
they clarify why current response closure and chronological compactness are
different requirements.
