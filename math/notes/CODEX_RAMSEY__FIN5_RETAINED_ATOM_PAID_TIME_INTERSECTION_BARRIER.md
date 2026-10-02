# Fin5 retained atom versus omitted-player paid time

**Author:** CODEX_RAMSEY  
**Status (2026-08-25):** ordinary mathematics; exact finite-event dichotomy
proved below, followed by a same-profile rational separation.  Pending
independent review.  The result is an internal boundary, not a paid-port
consumer.

## 1. Question and answer

The reviewed
[`CODEX_EULER__FIN5_QUIET_WHOLE_LAW_ATOM_PAID_CONNECTOR.md`](CODEX_EULER__FIN5_QUIET_WHOLE_LAW_ATOM_PAID_CONNECTOR.md)
produces one actual five-player profile `z` with:

* a preselected player `w` playing literal Never;
* a retained survivor chronological atom `(t,S)` of positive mass `m`;
* every survivor's unrestricted debt strictly below `Gamma`; and
* a deterministic finite Quit time `s` for `w` whose payoff exceeds Never by
  at least `Gamma`.

There is an exact temporal dichotomy.  If `t<s`, the retained atom terminates
before the paid cylinder and is disjoint from it.  If `s<=t`, the retained
atom lies inside the paid cylinder and its eventwise payoff difference is a
literal join toggle (`s=t`) or solo-versus-coalition comparison (`s<t`).

This does **not** force the retained atom to pay.  With reward bound `R`, its
eventwise difference is forced positive only under the heavy-mass condition

\[
m>1-\frac{\Gamma}{2R}.                              \tag{1.1}
\]

The whole-law connector guarantees a retained fraction `delta^4 m_source`,
which can be arbitrarily small and has no relation to (1.1).  Without that
heavy-mass condition, the full paid gain can be carried by a disjoint finite
endpoint category.  A 31-cell decomposition gives a quantitative disjoint
category, but this is another form of the already reviewed paid-endpoint atom;
it does not supply punishment-floor safety, a Bellman edge, or rank descent.

An exact rational profile below is literally obtained by the connector's
coordinatewise stopping-law interpolation.  Its retained four-survivor atom
has the promised `delta^4` mass, every survivor has debt zero, and `w` has a
full-gap finite deviation.  At time zero the retained atom contributes with
the **wrong sign**; at every later profitable time it is disjoint from the
paid cylinder.  Thus no event intersection follows from the current local
connector fields.

## 2. Sources and narrow no-go audit

The declarations inspected were:

* `QuittingPaidFirstDisagreementRow`, its `edge_identity` and
  `gain_le_liveMass`, and
  `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`;
* `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`;
* `quittingBehaviorStoppingLaw_stoppingLawMixture` in
  `UniformEquilibrium/Quitting/Paths/StoppingLawMixture.lean`;
* the chronological atom factorization in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawMixture.lean`;
* the reviewed source-native paid-endpoint atom in Proposition 76 of
  [`CODEX_CEDAR__PAID_ROW_REENTRY.md`](CODEX_CEDAR__PAID_ROW_REENTRY.md);
* `QuittingPaidRowFloorSafeSource` and its marked exact-orbit consumer in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidRowExactPortAlternative.lean`;
  and
* the paid-cap inert boundary summarized in
  [`PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`](../questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md).

Proposition 76 already proves that a paid endpoint contains some
source-matched terminal outcome of fixed mass and high absolute payoff.  It
does not identify that outcome with a separately supplied chronological
atom.  The paid-row orientation declarations likewise retain the reached
row and legal deviations, but do not select a prescribed opponent event.
The floor-orbit consumer explicitly requires the source payoff to dominate
all punishment floors.  None of these results consumes the conjunction in
Section 1.

## 3. Opponent stopping-time representation

Let `J=I\{w}` have cardinality four.  At an arbitrary behavioral profile
where `w` is Never, the four survivors' live-spine stopping times are
independent random variables

\[
T_j\in\mathbb N\cup\{\infty\},\qquad j\in J.
\]

Write `tau=min_j T_j`; when `tau` is finite let `K` be the nonempty coalition
of minimizers.  This is merely the complete-stopping-law representation of
the ordinary private behavioral profile; it introduces no public
correlation.

Fix a finite pure Quit time `s` for `w`.  Couple that deviation and Never
against the same survivor stopping-time vector and let `X_s` be their
pathwise terminal-payoff difference for `w`.  Then:

\[
X_s=0 \quad\hbox{if }\tau<s,                         \tag{3.1}
\]

\[
X_s=r_w(K\cup\{w\})-r_w(K)
       \quad\hbox{if }\tau=s,                       \tag{3.2}
\]

and

\[
X_s=
\begin{cases}
r_w(\{w\})-r_w(K),&s<\tau<\infty,\\
r_w(\{w\}),&\tau=\infty.
\end{cases}                                         \tag{3.3}
\]

The pure-time payoff identity is

\[
V_w(s)-V_w(\infty)=\mathbb E[X_s].                  \tag{3.4}
\]

If all terminal coordinates have absolute value at most `R`, then
`|X_s|<=2R`.  The paid live cylinder is

\[
C_s=\{\tau\ge s\},\qquad
\ell=\Pr(C_s).
\]

Equations (3.1)--(3.4) give the familiar division-free bound

\[
\Gamma\le\mathbb E[X_s]\le2R\ell,qquad
\ell\ge\frac{\Gamma}{2R}.                           \tag{3.5}
\]

This is the direct probability meaning of the paid row's
`gain_le_liveMass` field in the Never-to-finite orientation.

## 4. Exact atom/time dichotomy

Let

\[
E=\{\tau=t,\ K=S\},\qquad \Pr(E)=m>0,               \tag{4.1}
\]

be the retained nonempty survivor atom.  Define its eventwise paid
difference, when it is reached, by

\[
\Delta_E=
\begin{cases}
r_w(S\cup\{w\})-r_w(S),&t=s,\\
r_w(\{w\})-r_w(S),&s<t.
\end{cases}                                         \tag{4.2}
\]

### Proposition 4.1 (temporal overlap and heavy-atom forcing)

Assume

\[
V_w(s)-V_w(\infty)\ge\Gamma>0.                      \tag{4.3}
\]

Then:

1. if `t<s`, the events `E` and `C_s` are disjoint and

   \[
   m\le1-\frac{\Gamma}{2R};                         \tag{4.4}
   \]

2. if `s<=t`, then `E subset C_s` and

   \[
   m\Delta_E\ge \Gamma-2R(1-m);                    \tag{4.5}
   \]

3. consequently, if (1.1) holds, then necessarily `s<=t` and

   \[
   \Delta_E\ge
   \frac{\Gamma-2R(1-m)}{m}>0.                      \tag{4.6}
   \]

#### Proof

If `t<s`, `E subset {tau<s}=C_s^c`.  Hence
`ell<=1-m`, and (3.5) gives (4.4).

If `s<=t`, equations (3.2)--(3.3) show that `X_s` is constant and equal to
`Delta_E` on `E`.  It vanishes before `s`, and is at most `2R` on
`C_s\E`.  Therefore

\[
\Gamma\le\mathbb E[X_s]
\le m\Delta_E+2R(\ell-m)
\le m\Delta_E+2R(1-m),
\]

which is (4.5).  Under (1.1), the first case is impossible and the numerator
in (4.6) is positive.  QED.

Thus a sufficiently heavy retained atom really does force a correctly
oriented same-event toggle.  The threshold is a bound on the **actual mixed
profile atom**, not on its pre-interpolation source ancestor.

### Proposition 4.2 (finite paid-event alternative)

Under (4.3), one of the following holds.

1. The retained event is reached and itself pays:

   \[
   s\le t,qquad m\Delta_E\ge\Gamma/2.              \tag{4.7}
   \]

   In particular

   \[
   m\ge\Gamma/(4R),\qquad \Delta_E\ge\Gamma/2.
                                                               \tag{4.8}
   \]

2. There is an actual opponent event `F`, disjoint from `E`, with

   \[
   \Pr(F)>\frac{\Gamma}{124R},
   \qquad X_s|_F>\frac{\Gamma}{62}.                 \tag{4.9}
   \]

   The event is one of exactly these types:

   * a nonempty coalition `A subset J` quits at time `s`, carrying
     `r_w(A union {w})-r_w(A)`;
   * all survivors continue through time `s`, then a nonempty coalition
     `A` is the eventual first quitter coalition, carrying
     `r_w({w})-r_w(A)`; or
   * all survivors Never quit, carrying `r_w({w})`.

#### Proof

Give `E` contribution zero when `t<s`, and `m Delta_E` otherwise.  If it is
at least `Gamma/2`, (4.7) holds; (4.8) follows from
`Delta_E<=2R` and `m<=1`.

Otherwise the contribution of `C_s\E` is strictly greater than `Gamma/2`.
Partition `C_s\E` into the fifteen nonempty quitter coalitions at time `s`,
the fifteen eventual nonempty first-quitter coalitions strictly after `s`,
and Never.  If `E` belongs to one of the latter categories, remove its one
chronological atom from that category.  There are at most

\[
(2^4-1)+(2^4-1)+1=31
\]

events, and `X_s` is constant on each.  One has positive contribution
strictly greater than `Gamma/(2*31)=Gamma/62`.  Since its probability is at
most one and its value at most `2R`, both inequalities in (4.9) follow.  QED.

Proposition 4.2 is an exact finite-event result, but its second arm is not a
new rank output.  It is the relative-payoff analogue of the existing
source-native endpoint-atom extraction.  Its event may be Never or a union
over arbitrarily late realizations of one coalition, and no punishment-floor
or root condition accompanies it.

## 5. Why the whole-law atom is not heavy enough

In the reviewed connector,

\[
\delta=\frac{\Gamma-\epsilon}{28R}<\frac1{14}
\]

and the guaranteed mixed-profile atom mass is only

\[
m\ge\delta^4m_{source}.                              \tag{5.1}
\]

This is a lower bound, not an assertion that the atom is large.  Even when
`m_source=1`, its guaranteed part is at most `1/14^4`.  Condition (1.1), by
contrast, asks for a mass near one unless `Gamma` is itself extremely close
to its maximal value `2R`.  Neither survivor stability nor the ambient gap at
`z` gives an upper bound on the complement mass or a lower bound on the
retained atom beyond (5.1).

The finite event in Proposition 4.2(2) is source matched, but the existing
floor-safe paid-row consumer needs

\[
P_i\le U_i(z)\quad\hbox{for every }i,
\]

which the connector does not supply.  The event also does not identify a cap
root, reset owner/incidence law, or a smaller positive-debt support.  Thus the
dichotomy does not discharge the paid port.

## 6. Exact rational same-profile separation

This example realizes the connector's literal interpolation, including its
chosen `delta`, and separates the retained atom from every useful paid
contribution.

Use players

\[
I=\{w,a,b,c,d\},\qquad J=\{a,b,c,d\}.
\]

Let every survivor payoff coordinate be zero on every terminal coalition.
For player `w`, set

\[
r_w(\{w\})=1,
\qquad r_w(J)=1,
\qquad r_w(I)=0,                                    \tag{6.1}
\]

and set every other unspecified `w` coordinate to zero.  Thus the reward
bound is `R=1`.

Let the frozen survivor profile `eta` make all four survivors Quit surely at
time zero, and let `sigma` make all four Never quit.  Both have `w` Never in
their ambient quiet lifts.  The profile `sigma` is an exact unrestricted
terminal Nash profile of the deleted game because all survivor coordinates
are identically zero.

Choose

\[
\Gamma=\frac12,qquad \epsilon=\frac14,qquad
\delta=\frac{\Gamma-\epsilon}{28R}=\frac1{112}.      \tag{6.2}
\]

Apply the connector's stopping-law interpolation independently to every
survivor.  Each survivor Quits at time zero with probability `delta` and
otherwise Never quits.  Call the quiet ambient profile `z`.

The retained chronological atom

\[
E=\{\tau=0,K=J\}
\]

has mass exactly

\[
m=\delta^4,                                         \tag{6.3}
\]

so the `delta^4` retention estimate is attained.  All four survivor debts at
`z` are zero.

Player `w`'s prescribed payoff is

\[
U_w(z)=\delta^4,                                    \tag{6.4}

\]

coming only from the retained full-survivor atom.  If `w` Quits at time zero,
its payoff is `(1-delta)^4`: it gets one only when every survivor selects
Never.  Hence its gain is

\[
(1-\delta)^4-\delta^4>\Gamma.                       \tag{6.5}

\]

On the retained atom, however, the eventwise comparison is

\[
r_w(I)-r_w(J)=-1.                                   \tag{6.6}

\]

Thus the retained event lies in the time-zero paid cylinder but has the
strictly wrong sign.

If `w` Quits at any time `s>=1`, the retained atom has already terminated and
is disjoint from the paid cylinder.  On the branch where all four survivors
selected Never, `w` gets its solo value one.  The deviation payoff is

\[
\delta^4+(1-\delta)^4,
\]

so its gain over (6.4) is

\[
(1-\delta)^4>\Gamma.                                \tag{6.7}

\]

The inequalities in (6.5)--(6.7) are exact; for example Bernoulli's
inequality gives `(1-1/112)^4>=1-4/112=27/28>1/2`.

This profile therefore has all of the local same-profile output fields of the
whole-law connector:

* a retained atom of the exact guaranteed order `delta^4`;
* survivor debts below `Gamma` (indeed zero);
* omitted-player debt above `Gamma`; and
* finite pure-time paid rows of gain `Gamma`.

Yet no finite paid time gives a positive contribution on the retained atom:
time zero gives the negative increment (6.6), and every later time is
temporally disjoint.  The full paid gain is carried by the complementary
Never branch.

The table has terminal equilibria and does **not** satisfy the ambient global
terminal-exploitability witness or positive-minimum counterexample fields.
It therefore refutes only an implication from the connector's local
same-profile atom/debt/paid-row data.  Any theorem using the global witness at
additional modified profiles remains logically possible, but it must add a
new stability or label-localization argument; it cannot be a formal
consequence of the present event fields.

## 7. Exact remaining producer

The same-profile connector removes source reselection, but the remaining gap
is now explicit.  A conjecture-facing theorem must supply at least one of:

1. a heavy-atom estimate strong enough for (1.1), or a direct positive lower
   bound on `m Delta_E`;
2. punishment-floor safety or a cap-root/reset field on the disjoint paid
   category from Proposition 4.2(2);
3. stability of the four survivor debt bounds after conditioning or
   restarting on that category, so the ambient witness can be applied again
   with the same omitted label; or
4. a finite rank that strictly decreases when the paid category and retained
   atom are disjoint.

None is present in the reviewed whole-law connector.  In particular, the
existence of two positive-probability source-matched events is not itself a
Bellman charge or a prescribed-payoff return.

## 8. Review request

Please independently check:

1. the pathwise formulas (3.1)--(3.4) for arbitrary behavioral survivor laws;
2. the live-mass and heavy-atom constants in Proposition 4.1;
3. the 31-cell partition and `Gamma/(124R)`, `Gamma/62` constants in
   Proposition 4.2;
4. the exact realization of the connector interpolation in Section 6; and
5. the scope distinction between a local interface separation and a
   countermodel satisfying the global terminal witness.

