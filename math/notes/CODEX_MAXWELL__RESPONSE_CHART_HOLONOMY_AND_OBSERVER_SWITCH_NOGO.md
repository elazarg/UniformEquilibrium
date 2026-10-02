# Response-chart holonomy: exact seam decoding and the observer-switch no-go

Author: `CODEX_MAXWELL`

## Status

Ordinary mathematics, not checked in Lean.  The generic seam calculation is
exact and is a plausible small `MathUE` lemma.  Its quitting-game decoding uses
named checked pure-time and first-disagreement interfaces.  It does **not**
consume the remaining Fin4 minimum-response node.

The conclusion is a precise split which was implicit, but not proved, in the
finite Farkas formulation:

* an observer-balanced paid circulation necessarily produces an actual
  source-matched pure-time first-disagreement seam of fixed size;
* observer rotation is the only obstruction to that decoding at the scalar
  chart level; and
* the checked cyclic-plateau table realizes observer rotation with four exact
  local response charts, so neither freezing the observer nor decoding the
  scalar seams follows from the present local rectangle fields.

The regression has global minimum debt zero.  It is an interface no-go, not a
counterexample to a theorem that uses positive-minimum provenance in an
essential way.

**Disposition.**  The observer-balanced holonomy lemma is clean and
formalizable, but by itself it only reduces a circulation to the already
available generic paid-row node.  The plateau specialization sharpens the
known regression but remains a zero-minimum interface fence.  Neither part
should enter `exports/` without an additional positive-minimum adapter or a
consumer which retains the adjacent chart labels.  This note is ready for an
independent mathematical check as an internal no-go/reduction record.

## 1. Question

The reviewed minimum-response chord provides, at one actual source, a common
observer response rectangle and same-law minimum-source regeneration.  If
successive regenerated sources form a finite paid circulation, can one either

1. freeze one observer and one ordered pair of complete responses, obtaining
   a genuine vertex potential; or
2. convert every change of response witnesses into an actual source-matched
   chronological charge?

The answer is complete once the circulation is balanced separately by
observer.  Without that balance, the answer is no at the current interface.

## 2. Edge-local response charts

Let `V` be a finite set of literal source profiles `P_v`, and let `E` be a
finite directed multigraph with source and target maps `s,t : E -> V`.  An
edge `e` carries:

* a player `o_e`;
* two complete behavioral responses `a_e^-` and `a_e^+` of `o_e`; and
* a positive toll `c_e`.

For any vertex `v`, define the counterfactual response spread

\[
 \Psi_e(v)
 :=U_{o_e}(P_v[o_e\leftarrow a_e^+])
   -U_{o_e}(P_v[o_e\leftarrow a_e^-]).                 \tag{2.1}
\]

Assume the local rectangle orientation

\[
  c_e\le \Psi_e(t(e))-\Psi_e(s(e)).                    \tag{2.2}
\]

This is the abstract form of one common-response rectangle.  It is important
that `Psi_e` is defined at both literal endpoint profiles, not only at their
semantic carrier projections.

Let `lambda_e >= 0` be a nonzero circulation on the underlying graph:

\[
 \sum_{t(e)=v}\lambda_e=\sum_{s(e)=v}\lambda_e
 \qquad(v\in V).                                       \tag{2.3}
\]

Put

\[
 C:=\sum_e\lambda_ec_e,
 \qquad
 \Lambda:=\sum_e\lambda_e.
\]

Since every displayed toll is positive on the support, `C>0` and
`Lambda>0`.

## 3. Observer-balanced holonomy theorem

Assume:

1. `V` and `E` are finite;
2. every `P_v` is one actual behavioral profile for the same finite quitting
   reward table;
3. the two strategies on an edge are complete behavioral strategies of the
   displayed observer;
4. `lambda_e >= 0`, `Lambda > 0`, and (2.3) holds;
5. the weighted charge `C` is positive; and
6. the circulation is balanced not only at each vertex, but separately for
   each observer:

\[
 \boxed{
 \sum_{t(e)=v,\ o_e=i}\lambda_e
 =
 \sum_{s(e)=v,\ o_e=i}\lambda_e
 }
 \qquad(v\in V,\ i\in I).                              \tag{3.1}
\]

Then there exist a vertex `v`, one player `i`, and two complete behavioral
responses `b^- , b^+` of `i` such that

\[
 U_i(P_v[i\leftarrow b^+])-U_i(P_v[i\leftarrow b^-])
 \ge {C\over 2\Lambda}.                                \tag{3.2}
\]

In particular, if every toll on the circulation support is at least `c_0`,
then the right side is at least `c_0/2`.

### Proof

For fixed `(v,i)`, (3.1) gives equal total incoming and outgoing mass.  Couple
the incoming `i`-edges to the outgoing `i`-edges with any nonnegative
transport plan `mu_(e,f)` having the two `lambda` marginals.  For example, if
the common mass is `w>0`, use

\[
 \mu_{e,f}={\lambda_e\lambda_f\over w}.
\]

Summing the edge inequalities and regrouping by `(v,i)` gives

\[
\begin{aligned}
 C
 &\le \sum_e\lambda_e
      [\Psi_e(t(e))-\Psi_e(s(e))]\\
 &=\sum_{v,i}\sum_{\substack{t(e)=v,\ s(f)=v\\o_e=o_f=i}}
       \mu_{e,f}[\Psi_e(v)-\Psi_f(v)].                 \tag{3.3}
\end{aligned}
\]

The total mass of all the couplings is `Lambda`.  Hence some paired seam
satisfies

\[
 \Psi_e(v)-\Psi_f(v)\ge {C\over\Lambda}.               \tag{3.4}
\]

Because the observer is the same on the paired edges, the seam expands at
one literal profile into two legal same-player differences:

\[
\begin{aligned}
 \Psi_e(v)-\Psi_f(v)
 ={}&[U_i(P_v[i\leftarrow a_e^+])
      -U_i(P_v[i\leftarrow a_f^+])]\\
 &+[U_i(P_v[i\leftarrow a_f^-])
      -U_i(P_v[i\leftarrow a_e^-])].                   \tag{3.5}
\end{aligned}
\]

At least one bracket is at least half of (3.4).  Choosing its better and
worse strategies proves (3.2).  No cap attainment or compactness is used.

### Simple-cycle form

On a directed cycle of length `m` whose every edge has the same observer,
putting unit weight on the edges gives a seam gain at least

\[
 {\sum_e c_e\over 2m}.                                 \tag{3.6}
\]

If all edge charts use the same ordered response pair, every seam in (3.5)
is zero.  Therefore a positive paid cycle is impossible.  This is the exact
sense in which a source-coherent common-response chart orients the cycle.

## 4. Exact quitting-game decoding of a same-observer seam

The responses in (3.2) need not be pure times.  Fix the selected literal
profile `P_v`, observer `i`, and define

\[
 W(q):=U_i(P_v[i\leftarrow Q_q]),
 \qquad q\in\mathbb N\cup\{\infty\}.                  \tag{4.0}
\]

Here `q=infinity` is literal `Never`; no terminal time bound is imposed.  The
complete behavioral strategies `b^+` and `b^-` have stopping-law PMFs
`mu^+` and `mu^-` on `Option Nat`, and the checked stopping-law representation
gives exactly

\[
 U_i(P_v[i\leftarrow b^\pm])=\mathbb E_{\mu^\pm}W.     \tag{4.0a}
\]

The function `W` is bounded by the canonical quitting reward bound.  The
bounded-support-pair averaging lemma
`exists_support_pair_expect_sub_le_sub`, used in
`HasTerminalExploitabilityGap.exists_supported_pureTimePayoff_sub_at`,
therefore selects `q^+` in the support of `mu^+` and `q^-` in the support of
`mu^-`, with no loss:

\[
 V_i(q^+;P_v)-V_i(q^-;P_v)
 \ge {C\over2\Lambda}.                                 \tag{4.1}
\]

Both selected times may be finite, either one may be `Never`, and the finite
time may be arbitrarily large.  No compactness, attainment, tightness, or
bounded-clock substitution occurs.  Positivity rules out the case in which
the two selected plans are identical.  When the chart responses were already
pure times, this extraction is of course unnecessary.

Now
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` produces an
actual
`QuittingPaidFirstDisagreementRow` at the same literal source `P_v`, with the
same gain floor.  Its case split explicitly covers finite/finite,
finite/`Never`, and `Never`/finite witness orderings.  The terminal
payoff-difference atom decoder also gives a nonempty coalition carrying the
difference; the zero-reward `Never` terminal outcome cannot carry a positive
payoff difference.  Thus an observer-balanced
Farkas circulation cannot hide its chart holonomy as a merely formal scalar:

\[
 \boxed{
 \text{observer-balanced paid circulation}
 \Longrightarrow
 \text{source-matched paid pure-time seam row}.}
 \tag{4.2}
\]

This is a real chronology localization.  It is not yet a terminal consumer.
At current interfaces, the row can be cap-lifted and passed through the exact
paid-port trichotomy, but the counterexample regime still permits
quantitative descent or a literal inert stall.  Moreover, the terminal-gap
theorem already supplies a full-gap paid row at every actual profile.  The
new value in (4.2) is its derivation from, and attachment to, the two adjacent
response charts.  A theorem which forgets those chart labels gains no new
well-foundedness.

## 5. What fails when observers rotate

Without (3.1), (2.3) still permits regrouping the scalar expression at a
vertex, but an incoming chart and an outgoing chart may belong to different
players.  Then a numerical seam has the form

\[
 [U_i(P_v[i\leftarrow a^+])-U_i(P_v[i\leftarrow a^-])]
 -[U_j(P_v[j\leftarrow b^+])-U_j(P_v[j\leftarrow b^-])],
 \qquad i\ne j.                                        \tag{5.1}
\]

There is no algebraic decomposition of (5.1) into a profitable unilateral
change by one player at fixed opponents.  It is an interpersonal payoff
comparison.  The pure-time and first-disagreement decoders cannot be applied
to it.

The exact leftover is the observer-flow imbalance

\[
 b(v,i):=
 \sum_{t(e)=v,o_e=i}\lambda_e
 -\sum_{s(e)=v,o_e=i}\lambda_e.                        \tag{5.2}
\]

It satisfies

\[
 \sum_i b(v,i)=0\quad(v\in V),
 \qquad
 \sum_v b(v,i)=0\quad(i\in I),                         \tag{5.3}
\]

but these conservation laws have no strategic sign.  They describe rotation
of the observer label.  Finite pigeonhole does not remove it: a two-colour
alternating cycle has no monochromatic cycle.

Thus the exact finite alternative is

\[
\boxed{
\begin{array}{c}
\text{a common response chart (no paid circulation),}\\
\text{or an observer-balanced circulation with a paid seam row,}\\
\text{or a nonzero observer-rotation flow }b.
\end{array}}
\tag{5.4}
\]

The third arm is not another analytic escape.  It is a finite label-switch
obstruction.

## 6. Exact four-player observer-rotation regression

The checked table in
`Research/Quitting/FourPlayerCyclicPlateauCandidate.lean` realizes the third
arm.  Its sure-exit coalitions are

\[
 S_0=\{2\},\quad S_1=\{0,2\},\quad
 S_2=\{0,1,2\},\quad S_3=\{1,2\},                      \tag{6.1}
\]

with paid mover edges `S_k -> S_(k+1)` of gain `1`.

At a sure-exit row define the date-zero response spread

\[
 \delta_i(S):=r_i(S\cup\{i\})-r_i(S\setminus\{i\}).   \tag{6.2}
\]

The table gives, in cyclic phase order,

\[
 (\delta_0(S_k))_{k=0}^3=(1,1,-1,-1),
 \qquad
 (\delta_1(S_k))_{k=0}^3=(-1,1,1,-1).                 \tag{6.3}
\]

Use `QuitAt 0` minus `Never` when the sign below is positive, and reverse the
ordered pair otherwise.  The four edge charts are

\[
\begin{array}{c|c|c|c}
e&S_k\to S_{k+1}&o_e&\Psi_e\\ \hline
0&S_0\to S_1&1&\delta_1\\
1&S_1\to S_2&0&-\delta_0\\
2&S_2\to S_3&1&-\delta_1\\
3&S_3\to S_0&0&\delta_0.
\end{array}                                             \tag{6.4}
\]

Every chart increases from `-1` to `1`, so

\[
 1\le\Psi_e(S_{k+1})-\Psi_e(S_k)=2                   \tag{6.5}
\]

dominates the actual paid mover toll.  Unit edge weights give the Farkas
circulation.  At every vertex the incoming and outgoing observer labels are
different, so (3.1) fails maximally.  The apparent seams are interpersonal
comparisons of the form (5.1).

There is no fixed observer and fixed ordered pure-time pair orienting all four
edges.  At these sure-exit rows every deterministic plan is equivalent either
to Quit at date zero or to Continue at date zero; hence every fixed response
spread is `0`, `delta_i`, or `-delta_i`.  The increments of `delta_0` are

\[
 (0,-2,0,2),
\]

and the increments of `delta_1` are

\[
 (2,0,-2,0).
\]

Neither sequence, nor its negative, is positive on every edge.  Players `2`
and `3` have constant response spread and cannot orient an edge.  This proves
the exact local-interface failure

\[
\boxed{
\text{four source-matched local response rectangles}
\not\Longrightarrow
\text{one frozen observer/response chart}.}
\tag{6.6}
\]

The regression is all-behavior and literal: the checked declarations
`update_profile_phaseMover`, `phaseMover_payoff_gain`,
`nextPhase_mover_debt_eq_zero`, `phase_cap`, and
`phase_terminalOutcomeMass_eq_one` retain the actual unilateral updates,
caps, debts, and mass-one terminal atoms.  Its all-Continue profile is an exact
zero-debt equilibrium, so the global positive-minimum hypothesis is absent.

## 7. Consequence for the reviewed minimum-response chord

The export
`FIN4_MINIMUM_RESPONSE_CHORD_ATOM_AND_SOURCE_REGENERATION.md` supplies one
edge-local chart: one observer, one prescribed response, one pure-time
response, a positive rectangle, a retained atom, and same-law source
regeneration.  It does not assert either:

* observer balance (3.1) on a returned circulation; or
* literal preservation of the ordered response pair through the next
  source-to-paid construction.

Therefore neither alternative requested in Section 1 follows from the
current packet:

* exact freezing is falsified at the local interface by (6.6); and
* unconditional seam decoding stops at the observer-rotation flow (5.2).

If positive-minimum provenance separately forces (3.1), then Sections 3--4
immediately return a fixed-scale source-matched paid seam row.  But that row
still has to retain enough of its adjacent chart provenance to rule out the
ordinary inert paid-port branch.  Merely forgetting it into the generic paid
row type returns to an already-known atlas node.

## 8. Source audit

The bounded source set inspected for this note was:

* `exports/FIN4_MINIMUM_RESPONSE_CHORD_ATOM_AND_SOURCE_REGENERATION.md`;
* `exports/FIN4_MINIMUM_RESPONSE_CHORD_ACTUAL_LAW_REGENERATION.md`;
* `notes/CODEX_AMPERE__FINITE_STATE_ORIENTATION_FARKAS_AND_PLATEAU_NOGO.md`;
* `notes/CODEX_STOKES__OPEN_RESPONSE_CHORD_RENEWABILITY_TEST.md`;
* `MathUE/Optimization/SupremumTwoResetWitnessSwitch.lean`, especially
  `orientedSupremumWitnessSwitch_of_abs_mixedDifference` and
  `finiteCube_commonPassport_or_edgeWitnessSwitch`;
* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveSlopeRectangle.lean`,
  especially `quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff`
  and the two pure-time witness-switch constructors;
* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`,
  especially `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub`;
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`,
  especially `HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at`
  and `HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapPort`; and
* `Research/Quitting/FourPlayerCyclicPlateauCandidate.lean`.

No statement about the current response-chord export is being attributed to
the cyclic-plateau regression.  The regression checks only the necessity of
an additional positive-minimum/source-coherence argument.

## 9. Next exact question

Does positive-minimum Fin4 source provenance force observer balance (3.1) on
every returned paid circulation?  Equivalently, can a nonzero observer-rotation
flow (5.2) be decoded, using the exact debt-transfer identities at the shared
minimum source, into either

1. a support entry followed by a renewable zero-preserving elimination; or
2. a same-observer paid seam whose adjacent response-chart labels survive the
   paid-cap lift?

A result which merely produces another source-free paid row does not answer
this question, because such a row already exists with the full terminal gap
at every behavioral profile.

## 10. Review/export verdict

The following standalone statement merits formalization when useful:

> A finite observer-balanced circulation of edge-local response charts with
> positive weighted toll produces, at one literal vertex profile, a
> same-observer pure-time first-disagreement row of gain at least
> `C / (2 * Lambda)`, allowing `Never` and unbounded finite times.

It is a small generic transport-plus-averaging lemma and has a direct Lean
route through finite sums, `exists_support_pair_expect_sub_le_sub`, and
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub`.

It is **not currently export-worthy** under the conference gate.  Its output
is weaker than the full-gap paid row already available at every actual
profile, unless the two adjacent chart labels are retained and used by a new
consumer.  Likewise, the observer-rotation regression should remain an
internal no-go note: it identifies the exact missing finite passport, but its
minimum debt is zero and it eliminates no positive-minimum Fin4 branch by
itself.
