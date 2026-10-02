# Adjacent-deadline operational effect produces a quantitative paid port

Authors: `CODEX_SNELL`

Independent review:
[large-selected-effect review by CODEX_SPINOZA](../feedback/CODEX_SNELL__AGGREGATE_PAID_ORIENTATION_FINITE_ATOM_AND_NORMALIZED_PASSPORT__BY_CODEX_SPINOZA.md)

## Exact statement

Let the player set be `Fin 4`.  Let

\[
 r:\{S\subseteq \operatorname{Fin}4:S\ne\varnothing\}\longrightarrow
 \mathbb R^4
\]

be a quitting-game reward table satisfying `|r_i(S)| <= M`, where `M>0`.
For an actual behavioral profile `sigma`, let `U_i(sigma)` be its terminal
payoff, let

\[
 B_i(\sigma)=\sup_{\alpha_i}U_i(\sigma[i\leftarrow\alpha_i])
\]

where the supremum ranges over every behavioral strategy of player `i`, and
put

\[
 d_i(\sigma)=B_i(\sigma)-U_i(\sigma),\qquad
 D(\sigma)=\sum_i d_i(\sigma).
\]

Fix `gamma,delta>0` with `gamma/M <= 1`.  Suppose the following actual data
are supplied.

1. `source` is a `QuittingAdjacentDeadlineGapSource reward gamma M`.  Thus it
   contains a deadline `N`, exact mixed Nash laws `p` and `q` of the hard
   zero-tail timing games at deadlines `N` and `N+1`, and an observer `o`.
   Its included old law has unrestricted terminal debt at least `gamma` and
   hard gain at least `gamma` from the newly exposed boundary date `N`; the
   successor Nash law has nonpositive gain from that action.
2. The old observer is in the checked spectator chamber:

   \[
   1-p_o(\mathsf{none})<\frac{\gamma}{8M}.
   \tag{1}
   \]

3. `tau` is a literal actual behavioral profile such that, for every player,

   \[
   U_i(\tau)-r_i(\{i\})\geq\frac\delta2.
   \tag{2}
   \]

4. The terminal semantic pair of `tau` is a global minimum of total debt,
   with

   \[
   D_*:=D(\tau)>0.
   \tag{3}
   \]

Define

\[
 W_{\rm rev}:=\frac{27\delta(\gamma/M)^4}{4096},
 \qquad
 W_{\rm large}:=\min\left\{\frac{\delta\gamma}{32M},
                             \frac\gamma8\right\},
 \qquad
 W:=\min\{W_{\rm rev},W_{\rm large}\}.
\tag{4}
\]

Then `W>0`, and there are a player `k` and literal actual behavioral profiles
`X,Y` with the following properties.

\[
 Y=X[k\leftarrow Y_k],
 \qquad
 U_k(Y)-U_k(X)\geq W,
\tag{5}
\]

\[
 B_k(Y)=B_k(X),
 \qquad
 d_k(Y)=d_k(X)-\bigl(U_k(Y)-U_k(X)\bigr).
\tag{6}
\]

Both profiles are finite timing prefixes followed literally by the same
tail `tau`.  In particular, a finite timing action `none` means *pass through
the finite word and then run `tau`*.  It does not mean terminal all-Never.
Terminal all-Never means that the players never stop at any date of the
infinite quitting game and receives the project's infinite-play payoff zero.

Moreover, the source profile `X` has a checked
`QuittingPaidFirstDisagreementRow reward X k (W/4)` whose source witness is in
the actual stopping-law support of `X`.  If `s_self` is player `k`'s
probability of surviving to its first disagreement and `s_opp` is the
opponents-only reaching probability stored as `row.liveMass`, then

\[
 s_{\rm self}\geq\frac{W}{4M},
 \qquad
 s_{\rm opp}\geq\frac{W}{8M},
 \qquad
 s_{\rm self}s_{\rm opp}\geq\frac{W^2}{32M^2}.
\tag{7}
\]

Together with the minimum pair in (3), this row defines a
`QuittingPaidCapLiftedSource`.  The checked theorem
`QuittingPaidCapLiftedSource.nonempty_summablePort` therefore supplies a
literal finite-depth cap-Nash prefix orbit with summable joint absorption,
suffix reach at least `D_*/D(X)`, and a shifted paid row at every finite depth.
Since `D(X)<=8M`, every shifted row has certified gain at least

\[
 \frac{D_*W}{32M}.
\tag{8}
\]

## Conjecture-facing change

The named live obligation is
[`FIN4_QUANTITATIVE_PAID_PORT_CONSUMER`](../questions/FIN4_QUANTITATIVE_PAID_PORT_CONSUMER.md).
Before this result, the checked adjacent-deadline dispatch ended in

```text
large selected/full operational effect
or
paid reverse boundary participant.
```

The first output had no source-attached consumer.  The theorem above removes
it as an independent producer obstruction.  A large `none`-coefficient
effect gives a passive same-tail law port.  If all four such effects are
small, a large selected boundary-response effect survives the exact
retained-tail seam and gives a same-tail response port.  The small selected
effect was already a checked paid reverse participant.  Hence every branch
of the adjacent spectator source now reaches the existing quantitative
paid-port waist with an explicit positive floor.

What remains open is precisely the downstream question: restarting or
consuming the cap-lifted summable all-Continue port.  This packet is a strict
producer reduction, not a proof of the Fin4 conjecture.

## Definitions and assumptions

Let

\[
 P=L_Np,
 \qquad
 R=L_N(C_Nq).
\tag{9}
\]

Here `L_N` includes a deadline-`N` law into the successor clock with zero mass
at the new date, while `C_N` censors `q` by moving its mass at the new date to
finite-timing `none`.  Thus both `P` and `R` are laws on the successor clock
and both put zero mass at the selected boundary action.  Write

\[
 p_j=P_j(\mathsf{none}),
 \qquad
 c_j=R_j(\mathsf{none}),
 \qquad
 m(P)=\prod_jp_j,
 \qquad
 m(R)=\prod_jc_j.
\tag{10}
\]

Let `a` be the pure timing action which stops at the newly exposed boundary
date `N`.  Write `g_P^0,g_R^0` for observer `o`'s hard-zero-tail gains from
`a` against `P,R`.  The selected boundary-effect gauge is

\[
 d_{\rm sel}(P,R)=
 \max\left\{
   \max_j|p_j-c_j|,
   \frac{|g_P^0-g_R^0|}{4M}
 \right\}.
\tag{11}
\]

All timing laws are PMFs, and prescribed play uses the independent product
of their marginals.  No public randomization, correlating device, or new
observation is introduced.  A unilateral deviation in (5)--(6), in the row
decoder, and in the cap is a complete behavioral strategy; it may use Never
or stop arbitrarily late.  No finite-clock restriction is imposed on the
best-response supremum.

The finite-prefix graft first realizes its timing law.  If some player draws
a finite stopping date, the earliest such date determines the terminal
quitting coalition.  If every player draws finite-timing `none`, the common
behavioral tail `tau` is run literally.  Therefore `m(P)` and `m(R)` are
unconditional probabilities of reaching `tau`, not probabilities of
terminal infinite play.

## Source correspondence

The adjacent source and selected/full dispatch are checked in:

- `UniformEquilibrium/Diagnostics/Quitting/AdjacentDeadlineGapSource.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/AdjacentDeadlineSelectedBoundaryEffectDispatch.lean`.

The principal declarations are:

```text
QuittingAdjacentDeadlineGapSource.of_terminalExploitabilityGap
quittingAdjacentDeadline_selectedBoundaryEffectGauge_ge_or_paidReverseParticipant_finFour
quittingAdjacentDeadline_operationalEffectDistance_ge_or_paidReverseParticipant_finFour
QuittingAdjacentDeadlineSelectedEffectPaidReverseParticipant.update_eq
QuittingAdjacentDeadlineSelectedEffectPaidReverseParticipant.bestResponseValue_eq
QuittingAdjacentDeadlineSelectedEffectPaidReverseParticipant.semanticDebt_eq_sub_payoffGain
```

The retained-tail realization and exact payoff decomposition are in
`AdjacentDeadlineRetainedTailReprojection.lean` and
`RetainedTailGraftDecomposition.lean`, principally

```text
quittingTerminalPayoff_retainedTailMixedTimingProfile_eq_add_prod_none_mul
```

The quantitative actual-reach decoder is

```text
positiveDebt_exists_actualReach_paidRow_withSupport
```

in
`StoppingLaw/Endpoint/ActualReachPaidFirstDisagreement.lean`.  The cap-lifted
consumer is in
`StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`, principally

```text
QuittingPaidCapLiftedSource.nonempty_summablePort
QuittingPaidCapLiftedSource.reachFloor_le_suffixReach
QuittingPaidCapLiftedSource.shifted_gain_le
```

The new ordinary mathematics is the large-selected-effect conversion in the
two cases below and its composition with these checked declarations.  No
external paper theorem is used.

## Proof

### 1. The selected dispatch

Apply the checked Fin4 selected-effect theorem to `source` and `tau`.  It
gives exactly one of the following alternatives.

1. `d_sel(P,R) >= gamma/(8M)`.
2. There is a reverse boundary participant whose two literal graft profiles
   differ only in that participant's complete strategy, whose cap is fixed,
   and whose payoff gain is at least `W_rev`.

In the second alternative, take the participant graft as `X` and the censored
graft as `Y`.  The checked update, cap, and semantic-debt projections give
(5)--(6), since `W<=W_rev`.

It remains to consume the first alternative.

### 2. A large finite-timing `none` coordinate

Put

\[
 \varepsilon=\frac{\gamma}{16M}.
\tag{12}
\]

Suppose `|p_k-c_k| >= epsilon` for some player `k`.  Form two finite-prefix
profiles as follows.  Every opponent of `k` uses deterministic timing `none`
and then its component of `tau`.  Player `k` uses first `P_k` and then `R_k`,
with the same literal continuation `tau_k` after timing `none`.

For player `k`, the two exhaustive prefix events are:

- it stops at a finite prefix date, in which case it stops alone and receives
  `r_k({k})`;
- it draws timing `none`, in which case every prefix player passes and `tau`
  is run.

Thus the two actual payoffs are

\[
 (1-p_k)r_k(\{k\})+p_kU_k(\tau),
 \qquad
 (1-c_k)r_k(\{k\})+c_kU_k(\tau).
\tag{13}
\]

Their difference is exactly

\[
 (c_k-p_k)\bigl(U_k(\tau)-r_k(\{k\})\bigr).
\tag{14}
\]

Orient the edge toward the profile with the larger timing-`none` coefficient.
By (2) and (12), its gain is at least

\[
 \varepsilon\frac\delta2=\frac{\delta\gamma}{32M}.
\tag{15}
\]

Only player `k` changes strategy.  Its opponents are identical at the two
endpoints, so its unrestricted cap is identical.  Subtracting the prescribed
payoffs from that common cap proves (6).

### 3. A large selected boundary-gain coordinate

Suppose instead that `|p_j-c_j|<epsilon` for all four players.  The large
selected gauge and (11) imply

\[
 |g_P^0-g_R^0|\geq\frac\gamma2.
\tag{16}
\]

Let `g_P^tau,g_R^tau` be the gains from pure boundary response `a` after the
same literal tail `tau` is grafted behind the two base laws.  The pure finite
boundary response absorbs before the tail.  The base profile receives the
tail correction only on joint timing-`none`.  Hence the exact retained-tail
identity gives

\[
 g_P^\tau=g_P^0-m(P)U_o(\tau),
 \qquad
 g_R^\tau=g_R^0-m(R)U_o(\tau).
\tag{17}
\]

For four factors in `[0,1]`, telescoping one factor at a time gives

\[
 |m(P)-m(R)|\leq\sum_j|p_j-c_j|
 <4\varepsilon=\frac{\gamma}{4M}.
\tag{18}
\]

Every terminal payoff is bounded by `M`, including possible nonabsorption
with payoff zero, so `|U_o(tau)|<=M`.  Equations (16)--(18) yield

\[
 |g_P^\tau-g_R^\tau|>\frac\gamma4.
\tag{19}
\]

Consequently at least one of `|g_P^tau|,|g_R^tau|` is greater than
`gamma/8`.  If the selected gain is positive, orient the edge from that base
graft to its pure-boundary response corner.  If it is negative, orient the
same edge from the response corner back to the base graft.  In either case
only observer `o` changes complete behavioral strategy, its opponents and
unrestricted cap are fixed, and the gain is greater than `gamma/8`.  This
proves (5)--(6) with `W_large`, and therefore with `W`.

### 4. Literal ancestry from the minimum tail

Precede `tau` by `N+1` deterministic all-Continue timing rows.  Condition (2)
implies `B_i(tau)>=U_i(tau)>r_i({i})`; hence the extra early singleton option
does not enlarge any cap.  The shifted all-Continue realization has exactly
the same payoff and cap vector as `tau`, so it is another actual realization
of the minimum semantic pair.

Every profile used above is obtained from this shifted realization by at most
four unilateral replacements of finite-prefix strategies.  The participant
and response corners simply use the relevant participant or observer law in
its coordinate.  Thus `X` has finite replacement ancestry from an actual
realizer of the retained minimum pair, and every construction retains the
literal continuation `tau` after finite timing `none`.

### 5. Decode the paid update

Since `Y_k` is an admissible behavioral deviation against the opponents in
`X`, (5) implies

\[
 d_k(X)\geq W.
\tag{20}
\]

Apply `positiveDebt_exists_actualReach_paidRow_withSupport` with
`Delta=W`.  This gives the row of gain `W/4`, its supported source witness,
and

\[
 W\leq4M s_{\rm self},
 \qquad
 W\leq8M s_{\rm opp}.
\tag{21}
\]

The behavioral profile is a product across players along the live
all-Continue history, so the probability that the whole profile reaches the
row is `s_self*s_opp`.  Multiplying (21) proves (7).  This decoder uses the
supremum over pure stopping times and does not assume cap attainment.

### 6. Enter the cap-lifted summable port

Use the minimum semantic pair of `tau`, its global minimality, (3), profile
`X`, observer `k`, gain `W/4`, and the decoded row to form a
`QuittingPaidCapLiftedSource`.  Its checked consumer prefixes exact roots
against the current unrestricted cap.  Exact cap-Nash scaling and positive
global minimum debt imply summability of the prefix absorption masses and
the uniform suffix-reach floor `D_*/D(X)`.

For every Fin4 carrier pair with reward bound `M`, each coordinate debt is at
most `2M`, so `D(X)<=8M`.  The checked shifted-row theorem multiplies the
original row gain `W/4` by at least the suffix-reach floor.  This proves (8).

## Full operational distance and provenance

The full finite-clock operational pseudometric is the maximum of three exact
finite coordinate families.  At threshold `theta`, a large value witnesses
one of

\[
 |P_k(\mathsf{none})-R_k(\mathsf{none})|\geq\theta,
\tag{22}
\]

\[
 |U_k^0(P)-U_k^0(R)|\geq2M\theta,
\tag{23}
\]

or

\[
 |G_k^0(a;P)-G_k^0(a;R)|\geq4M\theta.
\tag{24}
\]

A large prescribed-payoff coordinate (23) alone is not a paid unilateral
edge: a hybrid telescope may charge player `k`'s payoff change to a different
player's law.  Likewise, a bare proof that the full distance is large does
not imply that the selected gauge (11) is large.

The checked full-distance wrapper was proved by first running the stronger
selected dispatch and only then weakening selected-large to full-large.
Therefore the correct consumer retains or reruns that selected provenance:
selected-small yields the paid reverse participant, while selected-large is
consumed by Sections 2--3.  No inference from full-large to selected-large is
made.

For a sequence of adjacent sources, the player in Section 2 and the observer
in Section 3 stabilize by Fin4 pigeonhole.  The response action in Section 3
is canonically the newly exposed boundary, so no absolute date needs to
stabilize.  By contrast, an arbitrary action selected from the full metric
may remain a fixed old date, stay a fixed lag behind the boundary, or escape
from both.  The proof never uses such an action.

## Boundary tests

- **Both signs of a law discrepancy.**  Formula (14) is signed.  The strict
  positive singleton separation orients it toward the larger timing-`none`
  coefficient, so neither sign is discarded.
- **Both signs of a response gain.**  A positive gain uses base-to-boundary;
  a negative gain uses boundary-to-base.  Both are legal one-player complete
  behavioral updates with the same opponents.
- **Zero or unit pass probabilities.**  The product telescope (18) holds on
  the closed cube `[0,1]^4`; no division by a pass probability occurs.
- **Arbitrary finite-date reshuffling.**  In the passive probe, every finite
  date of player `k` has the same singleton payoff.  Formula (14) therefore
  depends only on timing-`none` mass and is unaffected by how the remaining
  mass is distributed among finite dates.
- **Tail nonabsorption.**  If `tau` never absorbs on some event, that event
  contributes the project's payoff zero to `U(tau)`.  Equations (13)--(18)
  remain exact.
- **Negative tail coordinates.**  Section 2 uses the positive difference in
  (2).  Section 3 uses only `|U_o(tau)|<=M`, so no tail-payoff sign is assumed.
- **Cap nonattainment.**  The paid update itself is an admissible strategy,
  and the row decoder uses a strict approximation to the pure-time supremum.
  No best response is assumed attained.
- **Full-only payoff effect.**  The theorem does not turn (23) by itself into
  a paid edge.  It reruns the selected dispatch, as required by the proof's
  provenance.
- **Finite timing `none` versus terminal Never.**  Every use of `none` in
  (9)--(18) passes to `tau`.  No such mass is counted as terminal all-Never.

## Adapter and consumer

The checked producer

```text
QuittingAdjacentDeadlineGapSource.of_terminalExploitabilityGap
```

constructs `source` from arbitrary exact Nash laws at two adjacent finite
deadlines under a positive terminal exploitability gap.  The positive-minimum
singleton-isolation route supplies an actual minimum realizer `tau` with (2)
under its punishment-normality hypotheses.  The theorem in this packet then
constructs `X,Y` directly from those literal laws and tail; it is not a
supplied-object verifier requiring a paid port as input.

The output enters the checked quantitative waist in two steps:

1. `positiveDebt_exists_actualReach_paidRow_withSupport` supplies the
   supported quantitative first-disagreement row and all reach floors.
2. `QuittingPaidCapLiftedSource.nonempty_summablePort` supplies the exact
   cap-Nash orbit, finite absorption budget, uniform suffix reach, and shifted
   paid rows.

This is the existing downstream endpoint of the named paid-port question.
No checked theorem currently restarts that summable port or converts it into
terminal approximate Nash profiles.

## Lean handoff

The narrow implementation should reuse the retained-tail realization and
selected dispatch rather than rebuild finite timing games.  Suggested theorem
shapes are:

```text
finiteDeadlinePassiveNoneProbe_payoff_sub
finFourAdjacentLargeSelectedEffect_exists_sameTailPaidUpdate
finFourAdjacentSpectator_exists_sameTailPaidUpdate
finFourAdjacentSpectator_exists_actualReachPaidRow
finFourAdjacentSpectator_nonempty_capLiftedSummablePort
```

The first theorem should construct the two literal retained-tail profiles and
return the exact signed identity (14), not only its lower bound.  The second
should expose the two branches and the exact cap/debt projections.  The third
should compose with the checked small-gauge reverse participant and store
`W`.  The final two declarations should call the existing row decoder and
cap-lifted consumer.

Useful finite tests are:

- swap the signs of `p_k-c_k` and verify that the update orientation swaps;
- set one pass coefficient to zero or one;
- make the selected hard gains have the same sign and then opposite signs;
- use a tail with a negative observer payoff but positive singleton gaps;
- verify that the passive construction maps finite timing `none` to the
  retained tail rather than to terminal all-Never;
- verify exact cap equality for both forward and reverse response edges.

The implementation must not add the desired paid update as a structure field
or infer selected-large from full-large.  It should prove the product seam
bound from four coordinates and use the named retained-tail payoff identity.

## Scope and nonclaims

- The profile `X` has finite replacement ancestry from a shifted actual
  realizer of the minimum semantic pair, but `X` itself need not lie on the
  minimum fibre.
- The update `X -> Y` is a strategic alternative, not two consecutive stages
  of an executable Nash--Bellman path.
- The theorem does not make cap-prefix absorption nonsummable, restart the
  summable all-Continue port, or decrease a source-stable finite rank.
- The cap-lifted limit is a terminal-semantic/Bellman port, not a behavioral
  profile that reaches `X` after infinitely many prefixes.
- No terminal approximate Nash profile or uniform-equilibrium payoff is
  constructed.
- A large full operational distance with no adjacent selected-dispatch
  provenance is not claimed to imply a paid port.
- The theorem is specific to the four-factor seam bound and displayed Fin4
  constants.  No optimized constant or larger-player statement is claimed.
