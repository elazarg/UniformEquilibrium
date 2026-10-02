# Adjacent response reactivation: marked switch or remote bubble

Author: `CODEX_RESPONSE_SWITCH`

## Status

Ordinary mathematics, not checked in Lean.  Independent review by
`CODEX_GAUSS` returned **REVISE**.  The present version incorporates its
three required corrections: raw pure-time responses are not called literal
one-date siblings, the zero-minimum regression has a narrower conclusion,
and the iterated theorem/summary both state the fixed-observer, literal-label,
and uniform-scale hypotheses.  Delta review is pending.  This note is not an
export candidate.

The local response-switch theorem and the iterated clock/bubble calculation
below are complete under their stated source-coherence hypotheses.  They do
not prove Fin4 uniform equilibrium.

The main positive point is that a reactivated killed observer does not merely
produce an unnamed paid row.  If the incoming pure-time response is still the
prescribed response up to vanishing error, then the outgoing response supplied
by the endpoint-rise decoder beats that **same named incoming response** by the
full reactivated debt, up to the two displayed errors.  At a pure
nonsingleton marked row, the resulting first-disagreement chronology has only
two forms:

1. it is exactly the current marked date and is semantically a marked
   endpoint toggle (the actual pure marked profile can independently enter
   the checked no-tail screening consumer); or
2. the incoming response occurs strictly before the current mark, so the
   response clock strictly advances.

If the second form persists in a literally source-closed chain, the clocks
escape to infinity.  Fixed response gain then gives a uniform joint-survival
floor at the escaping disagreements, while the retained marked atom gives a
positive finite bubble at later dates.  Thus the whole infinite arm is a
quantitative remote-bubble/all-Never passport.

What is not yet checked is the Fin4 adapter proving that the current
source-faithful regenerated chronology makes the old shifted pure response
approximately prescribed at the *next* forced-pair source and retains that
identity through its pure-row normalization.  The exported source-faithful
causalization theorem retains the response as a counterfactual menu; the
additional installation estimate is expected from the vanishing absorption
of the common exact prefix plus literal equality of the regenerated suffix,
but it is not a public field.  Without it, the theorem below is conditional.

An exact Fin4 zero-minimum regression at the end shows that even literal
successor equality, fixed full-behavior response-square charge, exact debt
annihilation, and strictly increasing first-disagreement dates do not by
themselves force debt descent or preserve killed zeros along the displayed
chain.  It has an exact Nash profile elsewhere, so it is not a no-go against
a terminal-approximation disjunction.  Positive-global-minimum provenance
remains essential for the intended chain argument.

## 1. Exact question and inspected declarations

Fix a finite quitting table.  All caps below quantify over arbitrary complete
behavioral deviations.  Pure-time plans include `Never`.

The bounded source audit was:

* `FinFourMinimumResponseEndpointRiseOrigin`,
  `FinFourMinimumResponseRectangleSequence`, and
  `hasVanishingDebtAtomAlternative_of_endpointDebtRise` in
  `Research/Quitting/FinFourProducerAtlas/MinimumResponseChordActualDecoder.lean`;
* `FinFourMinimumResponseRectangle.responseChoice_ge_mark`,
  `routedStageMass_floor`, and the executable response profiles in
  `Research/Quitting/FinFourProducerAtlas/MinimumResponseChordRegeneration.lean`;
* `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`;
* the source-faithful causalization and arbitrary two-response menu transport
  recorded in
  `exports/SOURCE_FAITHFUL_MINIMUM_ENDPOINT_CAUSALIZATION_AND_RESPONSE_MENU_TRANSPORT.md`;
* `sameStageEndpointTrace_false_of_visitedSupport_card_le_four` and the Fin4
  monodromy eliminators summarized in `docs/FRONTIER.md`; and
* `FiniteResetCirculationRegression` and
  `FourPlayerCyclicPlateauCandidate` for the bounded-clock regressions.

The question is whether the response endpoint of one regenerated minimum
chart can be attached to the next chart strongly enough that reactivation of
the killed observer is either a persistent-zero contradiction or a genuinely
ordered response-switch seam.

### Public-adapter gap

The results below deliberately have two levels.

* Sections 2--3 are unconditional local theorems about supplied actual
  profiles and supplied pure-time responses.
* Section 4 is an iterated theorem about a supplied **literal source-closed
  response chain for one fixed observer**.

The current public Fin4 producer supplies neither the second level's
outgoing-to-next-incoming equality nor the installation estimate at the next
receiving profile.  It transports the incoming response as a counterfactual
menu item, which is weaker.  Thus Section 4 is not presently an adapter from
`FinFourMinimumResponseRectangleSequence`; proving that adapter is a
substantive remaining source-coherence obligation.

## 2. Installed-response reactivation identity

Let `A` and `B` be actual profiles which differ only in player `m`'s strategy,
with `m != o`.  Let `q^-` be a pure-time plan for observer `o` carried from the
preceding response chart, and let `q^+` be the new pure-time response chosen at
`B`.  Put

\[
 V_P(q):=U_o(P[o\leftarrow Q_q]).                       \tag{2.1}
\]

Assume the old response is installed at `B` with error `xi`:

\[
 |V_B(q^-)-U_o(B)|\le \xi.                              \tag{2.2}
\]

Exact installation is the case `xi=0`.  Suppose observer debt rises by
`kappa>0` across the horizontal edge,

\[
 d_o(B)-d_o(A)\ge\kappa,                                \tag{2.3}
\]

and the new response endpoint has debt at most `epsilon`:

\[
 d_o(B[o\leftarrow Q_{q^+}])\le\varepsilon.             \tag{2.4}
\]

Changing `o`'s own prescribed strategy does not change its unrestricted cap.
Therefore

\[
 V_B(q^+)=B_o(B)-d_o(B[o\leftarrow Q_{q^+}]).           \tag{2.5}
\]

Using (2.2)--(2.5) gives the exact quantitative seam

\[
\begin{aligned}
 V_B(q^+)-V_B(q^-)
 &\ge d_o(B)-\varepsilon-\xi\\
 &\ge \kappa+d_o(A)-\varepsilon-\xi\\
 &\ge \boxed{\kappa-\varepsilon-\xi}.
\end{aligned}                                           \tag{2.6}
\]

Thus whenever `epsilon+xi <= kappa/2`, the receiving profile `B`, named source
witness `q^-`, and named receiving witness `q^+` give a
`QuittingPaidFirstDisagreementRow` of gain `kappa/2`.  In addition, its target
`B[o <- q^+]` has observer debt at most `epsilon`.  This is stronger than an
anonymous paid row: the packet retains the preceding chart's response label,
the next chart's response label, the literal source and response endpoint,
and the vanishing-debt target.

The same proof works with signed one-sided installation

\[
 U_o(B)-V_B(q^-)\ge-\xi;                                \tag{2.7}
\]

rather than the absolute estimate (2.2).

### Why the source-faithful prefix should give `xi -> 0`

Suppose the preceding endpoint suffix literally prescribes `q^-`.  Prefix it
by an exact cap word `W`, while the shifted counterfactual response forces `o`
to Continue through `W` and then uses `q^-`.  Let `c(W)` be joint survival and
`c_{-o}(W)` opponent survival.  The source-faithful construction proves

\[
 c(W)\to1,\qquad c_{-o}(W)\to1.                         \tag{2.8}
\]

The prescribed profile and shifted response can differ only if the prefix
absorbs under one of those two plays.  For reward bound `R`, coupling gives

\[
 |V_{W*P}(\operatorname{shift}_Wq^-)-U_o(W*P)|
 \le 2R\bigl((1-c(W))+(1-c_{-o}(W))\bigr)\to0.          \tag{2.9}
\]

If the next pure-row normalization is literally idempotent on the retained
marked root, (2.9) survives it.  The current actualizer proves equality of
live-root sequences for its idempotent normalization, but the public
source-faithful regeneration object has not yet been composed with that
actualizer while exposing the shifted old response.  That composition is the
precise missing adapter, not a new cap estimate.

## 3. Pure nonsingleton rows force an exact clock-order split

Now assume `B` has a pure nonsingleton quitting coalition `C` at marked date
`t`.  Assume the new decoder response is late or Never:

\[
 q^+\in\{t,t+1,\ldots\}\cup\{\infty\}.                 \tag{3.1}
\]

This is exactly the order supplied by
`FinFourMinimumResponseRectangle.responseChoice_ge_mark` from the positive
response-law atom.

Suppose (2.6) is strictly positive.  There are exactly two cases.

### Mark-aligned switch

If also

\[
 q^-\in\{t,t+1,\ldots\}\cup\{\infty\},                 \tag{3.2}
\]

then the first disagreement is **exactly `t`**.

Indeed, both pure times Continue strictly before `t`.  At `t`, even after
overriding `o`, at least one member of `C\setminus\{o\}` still Quits surely,
because `|C|>=2`.  The continuation after `t` is therefore inaccessible under
both responses.  If the two responses also take the same action at `t`, their
payoffs are identical, contradicting (2.6).  Hence one Quits at `t` and the
other Continues there, which is precisely the first disagreement.

Conditional on reaching the marked row, the response switch is semantically
the same Boolean endpoint toggle: its receiving action is the strict better
endpoint and its routed coalition remains nonempty.  The two **raw pure-time
strategies are not literal one-date siblings**.  If, for example, one clock
is `t` and the other is `t+5`, they differ again at `t+5`; that later
difference is payoff-inaccessible because absorption at `t` is certain, but
it remains a difference of complete strategies.  Hence this raw switch is
not itself a `QuittingSameStageEndpointEdge`, and no literal common post-date
tail is asserted for it.

One edge alone is not a serial orbit.  The checked consumer applies under the
additional data actually needed by
`quittingFinFourPositiveMassNonsingleton_nonempty_screenedEndpoint`: a Fin4
global minimum `z_*`, global minimality of `D(z_*)`, `D(z_*)>0`, and a fixed
positive stage-mass floor `lambda` for this pure nonsingleton row.  Applied to
the same actual profile, date, and coalition, that theorem constructs the
entire no-tail screened serial orbit.  The checked Fin4 monodromy
impossibility eliminates its closed-segment arm, so the orbit ends at an
actual concentrated singleton while preserving the post-date tail of the
profile to which screening is applied.  This invocation is independent of
the raw response switch; the raw switch is not claimed to be the orbit's
internally selected first edge.  Alternatively one could first prove a
canonicalization lemma replacing the payoff-inaccessible later response
hazards by a common tail, but no such lemma is used here.

### Strict clock advance

Otherwise `q^-` is finite and

\[
 \boxed{q^-<t\le q^+.}                                  \tag{3.3}
\]

The first disagreement is exactly `q^-`.  In particular the outgoing response
clock is strictly later than the incoming response clock.  This is the only
way that a named response-switch seam avoids the mark-aligned chronology
case.  The resulting response endpoint is still independently eligible for
the weak concentrated screening output described below.

This split treats `Never` honestly.  If the incoming response is `Never`, it
belongs to the mark-aligned arm.  In the strict-advance arm the outgoing
response may be `Never`; after that, a further strict advance is impossible.

## 4. Iterated strict advance forces a quantitative remote bubble

Here is the exact conditional theorem.  Fix **one observer `o`**.  Assume a
literally source-closed sequence of its reactivations indexed by `k`:

* incoming pure time `q_k` and outgoing pure time `q_(k+1)`, in the extended
  order `N union {infinity}`;
* actual receiving profile `B_k` and response endpoint
  `D_k=B_k[o<-Q_(q_(k+1))]`;
* marked date `t_k` and a pure nonsingleton marked coalition;
* the exact payoff inequality

  \[
    U_o(D_k)-U_o(B_k[o\leftarrow Q_{q_k}])\ge g>0;
                                                               \tag{4.0}
  \]

* one fixed routed marked coalition `T` after a subsequence, with
  unconditional stage mass at least `lambda>0` in `D_k`; and
* literal response-label closure: the outgoing response `q_(k+1)` is the
  incoming response of the next retained occurrence of this same observer.

The indices may already form a subsequence of a larger regeneration chain.
Other observers may occur between two displayed ranks.  Requiring one fixed
observer is essential: without it, equality of successive pure-time labels
is not even a typed source-provenance statement.  No fixed-observer
extraction is inferred merely from finiteness; label installation through
the intervening charts is part of the stated hypothesis.

Suppose every rank lies in the strict-advance arm.  Then

\[
 q_k<t_k\le q_{k+1},                                    \tag{4.1}
\]

so every displayed `q_k` is finite and `q_k` and `t_k` tend to infinity.  If
some outgoing clock were `infinity`, the next strict-advance inequality could
not hold, and the infinite arm would already have terminated.

Let `R` bound the absolute value of every terminal reward.  Since `g>0`, one
may take `R>0`.  Let `L_k` be the probability, against the opponents in
`B_k`, that all opponents survive to the live history at `q_k`.  Before
`q_k`, both pure responses in (4.0) Continue.  Conditional on reaching their
first disagreement, their terminal payoffs lie in `[-R,R]`.  Therefore the
elementary first-disagreement bound (and, equivalently, the checked decoder)
gives

\[
 g\le 2R\,L_k,                                          \tag{4.2}
\]

Hence

\[
 L_k\ge \rho:=\frac{g}{2R}>0.                           \tag{4.3}
\]

In the receiving endpoint `D_k`, observer `o` also Continues surely before
`q_k` because `q_(k+1)>q_k`.  Its opponents are unchanged from `B_k`.
Therefore the probability under the actual prescribed profile `D_k` that
**all players** reach the live history at `q_k` is exactly `L_k`, and is at
least `rho`.

Now pass once to a common subsequence with all of the following properties:

1. every player's complete stopping law converges weakly on the compact
   one-point compactification `N union {infinity}`;
2. the finite terminal-outcome laws of `D_k` converge in the finite
   coalition simplex to a law `nu`; and
3. the already stabilized routed terminal is the same `T` and its marked
   mass is at least `lambda` at every retained rank.

The limiting marginal laws determine a literal product behavioral profile
`bar_sigma` (using the usual hazard reconstruction, with arbitrary hazards
after a zero-survival prefix).  For every fixed date `N`, eventually
`N<q_k`.  Survival through `N` depends on only finitely many marginal clock
coordinates, so finite-prefix continuity gives

\[
 \Pr_{\bar\sigma}(\hbox{all players survive through }N)\ge\rho.
\]

Letting `N` tend to infinity yields

\[
 \boxed{\Pr_{\bar\sigma}(\hbox{all players Never})\ge\rho.}          \tag{4.4}
\]

This records exactly what survives marginal compactification: each marginal
stopping law is the weak limit of the corresponding marginal in `D_k`, and
the resulting **actual product profile** has all-Never mass at least `rho`.
It does not claim that its full terminal law equals `nu`.

At the same time, (4.1) implies `t_k->infinity`, and the marked `T`-atom has
mass at least `lambda`.  For every fixed cutoff `N`, eventually `N<t_k`.
The marked event is then disjoint from all `T`-absorptions by time `N`, so

\[
 \operatorname{Law}(D_k)(T)
 \ge \Pr_{D_k}(T\hbox{ absorbs by }N)+\lambda.
\]

The event on the right is a finite-prefix event.  Taking `k` to infinity
along the common subsequence gives

\[
 \nu(T)\ge
 \Pr_{\bar\sigma}(T\hbox{ absorbs by }N)+\lambda.
\]

Monotone convergence in `N` gives the exact escaped-mass bound

\[
 \boxed{\nu(T)-\operatorname{Law}(\bar\sigma)(T)\ge\lambda.}         \tag{4.5}
\]

Thus an infinite pre-mark response-switch chain is not an unstructured
collection of paid rows.  It produces one selected compact limit with:

* positive all-Never mass at least `rho` in the actual compactified product
  profile;
* escaped finite coalition mass at least `lambda` in one named terminal
  coordinate;
* the old/new response labels and the ordered disagreement dates; and
* the literal source/minimum passport stored by the incoming chain (this is
  external provenance; neither `bar_sigma` nor `nu` is thereby asserted to
  attain that minimum).

This is the remote-bubble/all-Never node isolated by the strict-ray analysis.
The scalar jump at that node is not presently oriented: the exact identity
in `CODEX_RIEMANN__REMOTE_BUBBLE_ALL_NEVER_JUMP_REGRESSION.md` shows that
bubble reward minus cap jump is just the difference between the actual
all-Never debt and the bubble semantic debt.  Global minimality supplies the
opposite weak order from the one needed for a direct contradiction.

Accordingly, (4.4)--(4.5) are a genuine compactness output but **not a
consumer of the remote-bubble arm**.  Any source theorem advertising the
bubble as a return, a minimum point, or a terminal approximation would be
stronger than what is proved here.

There is also a simpler checked output at every individual rank.  Since
`q_(k+1)>=t_k`, the actual profile `D_k` has a pure routed marked coalition.
If that coalition is a singleton, a concentrated endpoint is already
present.  If it is nonsingleton, its mass floor `lambda`, the positive global
minimum, and
`quittingFinFourPositiveMassNonsingleton_nonempty_screenedEndpoint` produce a
concentrated singleton directly from `D_k`.  Thus the remote-bubble theorem
is not needed to obtain the existing weak concentrated endpoint.  Its extra
content is the fixed-observer ordered response history and the quantitative
mismatch between limiting marginals and the full terminal law.  Retaining
that stronger incoming response/minimum passport through the screened output
is a separate unproved adapter.

## 5. Exhaustive adjacent-chart reduction

Here is the correctly quantified reduction.  Fix one observer `o` and a
retained sequence of its regenerated charts.  Assume at every displayed rank:

* the installed-old-response estimate (2.7) and the endpoint debt estimates
  give the **same fixed** response-switch floor `g>0` whenever `o` is
  reactivated;
* the outgoing response label is literally the incoming label at the next
  displayed occurrence of `o`, including transport through any intervening
  charts; and
* the actual response endpoint has one stabilized routed coalition with the
  **same fixed** marked mass floor `lambda>0`.

Then a previously killed `o` at each next endpoint has the following local
fate:

\[
\boxed{
\begin{array}{c}
\text{its debt remains zero;}\\
\text{or its named old/new response switch has gain at least }g,\\
\qquad\text{and the new-response target has vanishing observer debt.}
\end{array}}
\tag{5.1}
\]

Every response target in the second arm already gives a weak concentrated
singleton endpoint: directly if its routed mark is singleton, or by the
checked no-tail screening theorem if it is nonsingleton.  For the stronger
chronological passport, Section 3 further divides its raw response switch:

\[
\boxed{
\text{mark-aligned semantic endpoint toggle}
\quad\lor\quad
q_k<t_k\le q_{k+1}.}
\tag{5.2}
\]

If the strict second arm occurs at every rank of this fixed-observer,
label-closed, uniform-`g`, uniform-`lambda` sequence, it yields (4.4)--(4.5).
Without any one of those four cross-chart hypotheses, “repeats
source-faithfully” is insufficient: gains or marked masses may vanish, or the
successive clocks may not be comparable.

Thus the checked weak endpoint is already concentrated, while the genuinely
new conditional normal form is

\[
\boxed{
\text{persistent killed zero}
\quad\lor\quad
\text{source-attached concentrated endpoint}
\quad\lor\quad
\text{fixed-observer quantitative remote bubble}.}
\tag{5.3}
\]

The last disjunct records stronger chronology and compactness data; it is not
a terminal consumer.  Preservation of the full incoming source passport
through the concentrated-screening wrapper also remains open.

The important missing Lean/source statement is no longer a generic
first-disagreement decoder.  It is:

```text
sourceFaithfulResponseEndpoint_oldResponse_installationError_tendsto_zero
```

composed with the next actual endpoint-rise origin on the same chronology and
mark.  It must expose the shifted old pure time, not merely an arbitrary
historical response menu.

## 6. Exact zero-minimum escaping regression

The following rational Fin4 table shows why a bare response seam does not
force chain-local debt descent or preservation of previously killed zeros.
Players `0,1` are active and players `2,3` are dummy players.  Put

\[
 r_0(S)=\begin{cases}-1,&0\in S,\ 1\notin S,\\0,&\text{otherwise},\end{cases}
\qquad
 r_1(S)=\begin{cases}-1,&1\in S,\ 0\notin S,\\0,&\text{otherwise},\end{cases}
\tag{6.1}
\]

and `r_2=r_3=0`.  Dummies play `Never`.

For `r>=0`, define four-corner profiles by the active pure times

\[
 A_r=(2r,2r+1),\quad
 B_r=(2r+2,2r+1),\quad
 C_r=(2r,2r+3),\quad
 D_r=(2r+2,2r+3).                                      \tag{6.2}
\]

Then `D_r=A_(r+1)` literally on the two active players (and on the dummy
players as well).  The horizontal mover is player `0`, and the observer is
player `1`.  Direct pure-time enumeration, which is complete for behavioral
caps in a quitting game, gives

\[
 d(A_r)=(1,0,0,0),\qquad d(B_r)=(0,1,0,0),\qquad
 d(D_r)=(1,0,0,0).                                     \tag{6.3}
\]

Player `0` gains one on `A_r -> B_r`.  Player `1` changes from incoming
response `2r+1` to outgoing response `2r+3`, gains one on `B_r -> D_r`, and
kills its debt exactly.  At the source sibling `A_r`, the same response change
has gain zero.  Hence every rectangle has exact response cross charge one:

\[
 [U_1(D_r)-U_1(B_r)]-[U_1(C_r)-U_1(A_r)]=1.             \tag{6.4}
\]

The first-disagreement dates `2r+1` tend strictly to infinity, the target is
literally the next source, every gain is fixed, and total debt remains one.
All marginal clocks converge to `Never`; every `D_r` has terminal law equal
to the unit mass at `{0}`, so the compact limit has a unit `{0}` bubble.

The all-Never profile is an exact terminal Nash profile: active players weakly
prefer `Never` with payoff zero to quitting alone for `-1`, while the dummies
are indifferent.  Therefore

\[
 \boxed{D_*=0.}                                        \tag{6.5}
\]

This does not refute a positive-minimum adjacent-chart theorem.  Moreover it
does **not** refute a disjunction allowing terminal approximations: all-Never
is already an exact terminal Nash profile.  What it does falsify is the
narrow chain-local implication

\[
\begin{array}{c}
\text{literal successor-closed four-corner response squares}\\
+\ \text{exact full-behavior caps, fixed cross charge, exact debt kills}\\
+\ \text{strictly ordered escaping first-disagreement chronology}
\end{array}
\Longrightarrow
\begin{array}{c}
\text{some displayed successor has lower total debt, or}\\
\text{a zero killed at one corner remains zero after regeneration.}
\end{array}                                                            \tag{6.6}
\]

Indeed all displayed total debts equal one, while the zero of player `0` at
`B_r` is reactivated at `D_r`, and the zero of player `1` at `D_r=A_(r+1)`
is reactivated at `B_(r+1)`.

The existing bounded-date reset and Fin4 plateau regressions complement this
example: bounded response labels can circulate as well.  Thus the split
between bounded/mark-aligned and escaping clocks is mathematically real, and
positive-minimum provenance must be used after the split rather than merely
to guarantee the local seams.

The marked terminal in this regression is a singleton, not a nonsingleton.
It is therefore a no-go for the proposed *bare response-seam interface*, not
a counterexample to the pure-nonsingleton clock-order theorem of Section 3.

## 7. Comparison with the singleton-clock Jensen branch

`SERIAL_ENDPOINT_AUDITOR__VANISHING_JENSEN_CLOCK_COMPRESSION.md` disintegrates
one singleton owner's prescribed stopping law:

\[
 \sigma=\sum_t\alpha_t\sigma^t,
\]

and defines the outsider-cap Jensen loss

\[
 J_i=\sum_t\alpha_t B_i(\sigma^t)-B_i(\sigma)\ge0.      \tag{7.1}
\]

Its `J_i -> 0` arm already co-selects a deterministic-clock component with
both a singleton stage-mass floor and debt tending to `D_*`.  The question is
whether the present response-switch machinery consumes the complementary
fixed-curvature arm.

There is an exact source-matched switch hidden in positive Jensen curvature.
For each `t`, choose a pure time `q_t` which is `epsilon`-optimal for player
`i` at `sigma^t`.  Let `T,S` be independent with law `alpha`.  Fixed-response
payoff is affine in the owner's mixture, so

\[
 \mathbb E_{T,S}V_T(q_S)
 =\mathbb E_S V_\sigma(q_S)
 \le B_i(\sigma).                                      \tag{7.2}
\]

On the other hand,

\[
 \mathbb E_TV_T(q_T)
 \ge\sum_t\alpha_tB_i(\sigma^t)-\varepsilon.           \tag{7.3}
\]

Subtracting gives

\[
 \mathbb E_{T,S}\bigl[V_T(q_T)-V_T(q_S)\bigr]
 \ge J_i-\varepsilon.                                  \tag{7.4}
\]

Hence some two deterministic owner clocks `s,t` satisfy

\[
 \boxed{V_t(q_t)-V_t(q_s)\ge J_i-\varepsilon.}          \tag{7.5}
\]

This is a genuine same-profile, two-pure-time response switch, with receiving
target `sigma^t[i<-q_t]` having `i`-debt at most `epsilon`.  The current
first-disagreement decoder applies with the two named witnesses.  Thus the
positive-Jensen arm does not lack a response-switch decoder.

It lacks **co-realization with the minimum singleton passport**.  Let

\[
 A=\{t:s_t\ge\mu/2\}
\]

be the good singleton-mass clocks from the Jensen note.  The weighted
selection theorem proves `alpha(A)>=mu/(2-mu)`, but (7.4) may be carried
entirely by pairs whose receiving clock `t` lies outside `A`.  Even if one
forces `t in A` by an additional quantitative domination hypothesis, positive
Jensen loss says

\[
 \sum_t\alpha_t(D(\sigma^t)-D_*)
 =D(\sigma)-D_*+J,
\]

so the response-switch component need not be near the minimum fibre.  The
existing source-faithful response-chord machinery begins only after the
receiving response endpoint and its marked law are on that fibre.

Therefore the machinery in this note does **not** consume persistent Jensen
curvature from the stated hypotheses.  The precise missing theorem is a
three-way co-realization:

\[
\boxed{
J_i\ge\kappa
\Longrightarrow
\begin{array}{c}
\text{a fixed switch (7.5) at a mass-good, near-minimum component},\\
\text{or a source-faithful reprojection of its response endpoint to }D_*,\\
\text{or a strict finite-rank/minimum-support transition.}
\end{array}}
\tag{7.6}
\]

The first arm would feed Sections 2--5 directly.  Merely returning (7.5)
without the mass/minimum fields is another paid row and does not close the
Jensen branch.  This is exact agreement with the Jensen note's stated
boundary, now with the strongest automatic pairwise switch (7.5) made
explicit.

## 8. Lean-facing boundary

The local declaration should be generic:

```text
quittingPureTime_responseSwitch_gain_of_installed_of_debtRise
```

returning the old/new pure times, the exact payoff lower bound (2.6), the new
target-debt bound, and a `QuittingPaidFirstDisagreementRow` whose source and
receiving witness equal those named times.

The pure-row declaration should return a sum type:

```text
quittingNonsingletonResponseSwitch_marked_or_clockAdvance
```

with either first-disagreement date exactly the mark and semantic equality to
the corresponding marked endpoint toggle, or `old < mark <= new`.  A literal
`QuittingSameStageEndpointEdge` would require an additional canonicalization
of the payoff-inaccessible later response hazards; the present note instead
invokes no-tail screening independently on the actual pure marked profile.

The source-level Fin4 theorem should then be:

```text
FinFourSourceFaithfulResponseRegeneration.
  persistentZero_or_concentratedSingleton_or_remoteBubble
```

Its nontrivial hypotheses/fields are the pointwise installation estimate and
literal outgoing-to-incoming response label equality.  The response-menu
transport export already supplies the payoff scaling needed before the next
inner marked update; it does not yet expose these two dependent equalities.

## 9. Nonclaims

This note does not:

* prove the installation adapter from the current public Fin4 source object;
* orient the remote bubble's reward/cap jump;
* consume the concentrated-singleton packet;
* turn a horizontal response switch into an exact Nash--Bellman edge;
* prove persistent-zero preservation; or
* prove or refute the finite-quitting uniform-equilibrium conjecture.

## 10. Conclusion

The strongest unconditional new theorem here is the local installed-response
identity (2.6), followed at a pure nonsingleton row by the exact clock-order
split (3.3).  This upgrades observer reactivation from an anonymous paid row
to a named old-response/new-response seam with a vanishing-debt target.

Every supplied response endpoint with the fixed marked-mass floor already
enters the checked Fin4 no-tail screening consumer when its routed coalition
is nonsingleton, and is already concentrated when that coalition is a
singleton.  This does not by itself preserve the stronger incoming response
passport.  With a supplied fixed-observer source-closed chain, the additional
chronology says that infinitely many pre-mark occurrences yield the
quantitative all-Never/bubble passport (4.4)--(4.5).  The latter is not
consumed.

The exact missing public producer is the dependent adapter which installs the
old shifted response at the next receiving endpoint and proves literal
outgoing-to-next-incoming label closure for one fixed observer, possibly
through intervening charts.  Positive Jensen curvature supplies a pairwise
response switch but not this mass-good/minimum/source co-realization.
