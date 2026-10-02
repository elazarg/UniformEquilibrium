# Review of persistent-reentry diagonal cap square

Reviewer: `CODEX_BANACH`

## Verdict

**REVISE.**  The diagonal-square algebra, its cap anchors, the exact
cross-corner debt identity, and the rational regression are correct.  The
minimum-return paragraph currently suppresses two hypotheses which do not
follow from historical-label retention or compactness:

1. convergence of the displayed diagonal endpoints to the global minimum
   fibre; and
2. a positive finite terminal atom in the limiting killed-observer endpoint
   law (preferably a fixed terminal with a uniform mass floor).

With those hypotheses added, the equality arm does give the claimed proper
minimum chord, strict killed-observer support handoff, and source regeneration.
Without the second one, the support statement remains valid but
`FinFourMinimumAtomProducer.regeneratedAtLawPoint` cannot be invoked.  Without
the first one, global minimality does not put either endpoint or its chord on
the minimum fibre.

The note is not exportable after this repair.  It remains a conditional local
normal form whose source-attached trace is not produced by the current public
Fin4 records, and neither arm is consumed into a terminal approximation,
admissible return, or renewable rank decrease.

## Claim checked

For one fixed observer `o`, actual base profiles `P_k`, and three consecutive
pure-time labels `q_k,q_(k+1),q_(k+2)` in a common absolute clock, assume the
old-to-new response gain at each displayed base is at least `g>0` and the new
response endpoint has observer debt at most `epsilon_k -> 0`.  The note claims:

* an exact positive response-value square across adjacent bases;
* an exact own-debt drop from the reactivated old-response corner to the next
  response endpoint;
* conditional localization to one literal nonobserver edit when a bounded
  edit trace is supplied;
* an off-minimum/minimum alternative after joint compactification; and
* in the minimum arm, a proper minimum response chord with a strict support
  handoff and regenerated minimum sources.

It also gives a rational `D_*=0` regression showing that even a fixed positive
diagonal charge, exact cap attainment, equal diagonal semantic pairs, equal
diagonal laws, and constant support do not themselves produce the desired
chronology or rank.

## 1. The diagonal algebra and cap anchors are correct

Write

\[
 V_k(q)=U_o(P_k[o\leftarrow Q_q]),
 \qquad B_k=B_o(P_k).
\]

Own-strategy cap invariance gives

\[
 d_o(P_k[o\leftarrow Q_{q_{k+1}}])
   =B_k-V_k(q_{k+1}).
\]

Thus the near-cap hypothesis implies

\[
 V_k(q_{k+2})-V_k(q_{k+1})\le\varepsilon_k,
\]

because every pure-time payoff is bounded above by the unrestricted
behavioral cap.  The next-base gain gives

\[
 V_{k+1}(q_{k+2})-V_{k+1}(q_{k+1})\ge g.
\]

Subtraction therefore proves exactly

\[
 C_k=
 [V_{k+1}(q_{k+2})-V_{k+1}(q_{k+1})]
 -[V_k(q_{k+2})-V_k(q_{k+1})]
 \ge g-\varepsilon_k.
\]

The reentry identity is also correctly oriented:

\[
 C_k=ell_k(q_{k+1})-\ell_k(q_{k+2}),
 \qquad
 \ell_k(q)=V_k(q)-V_{k+1}(q).
\]

No stationary or bounded-deviation substitution occurs here.  The only use
of best response is the full behavioral cap bound on pure-time responses.

The commuting-profile-square qualification is correct.  If the horizontal
transformation changes no `o` coordinate, response replacement by `o`
commutes literally with it.  Without that source-level fact, the four payoff
numbers still satisfy the identity, but the profiles need not be the corners
of one commuting unilateral square.

## 2. The cross-corner debt identity is exact

Let

\[
 E_k=P_{k+1}[o\leftarrow Q_{q_{k+1}}],
 \qquad
 D_{k+1}=P_{k+1}[o\leftarrow Q_{q_{k+2}}].
\]

Their opponents are identical, so their unrestricted `o`-caps agree.  Hence

\[
 d_o(E_k)-d_o(D_{k+1})
 =U_o(D_{k+1})-U_o(E_k)
 \ge g.
\]

This is stronger than an anonymous paid row: it is one actual complete
own-strategy replacement between two named pure-time responses.  At finite
rank the outgoing response is only *approximately* cap-attaining, however.
The phrase "displayed full-cap response" should therefore be replaced by
"displayed near-cap response endpoint"; exact cap attainment holds only in
the limit after the debt tends to zero.

Historical-label retention, with the exact prefix shifts from
`CODEX_DARBOUX__ADJACENT_RESPONSE_INSTALLATION_TRACE.md`, is sufficient to
define this actual `E_k` sequence.  It is not sufficient for the subsequent
minimum and law claims.

## 3. Compactness does not supply minimum provenance

Joint semantic/law compactness supplies a common refinement on which `E_k`
converges.  If `D_{k+1}` already converges, this refinement preserves its
limit.  Compactness alone does **not** prove

\[
 D(D)=D_*.
\]

That equality must be assumed or obtained from a named source theorem showing
that the displayed diagonal endpoint family has total debt tending to `D_*`.
The three assumptions in Section 1 of the note only control one coordinate's
endpoint debt; they do not control total debt.  Section 4 later states the
needed minimum-fibre assumption, but Section 1.1 currently uses it before
stating it as an additional hypothesis.

After adding

\[
 D(D_{k+1})\longrightarrow D_*,
\]

the dichotomy is valid.  Continuity gives `d_o(D)=0`; the exact debt identity
gives `d_o(E)>=g`; actual-carrier membership and global minimality give
`D(E)>=D_*`; hence exactly `D(E)>D_*` or `D(E)=D_*`.

The strict arm should be described as a cofinal family of actual
off-minimum-to-near-minimum response updates with limiting endpoints `E,D`.
The limit points themselves may be unattained, so "an actual ... cap response"
between the two limit points is too strong if read literally.

## 4. The equality-arm support theorem needs a positive limiting atom

Assume now that both limit endpoints are on the minimum fibre.  Since `E_k`
and `D_{k+1}` differ only in `o`'s complete strategy, proper behavioral
mixtures of those two stopping laws are executable.  Fixed deviations of
players other than `o` are affine in the opponent mixture and their caps are
convex; the `o`-cap is constant.  Therefore coordinate debt is bounded above
by the affine endpoint debt.  Global minimality plus equality of both endpoint
debt sums forces equality coordinatewise, exactly as in
`QuittingMinimumResponseChordLaw.chord_debt_eq_affine` from
`Research/Quitting/MinimumResponseChordLaw.lean`.

Consequently every proper chord point `H_theta` has

\[
 \operatorname{supp}^+d(H_\theta)
 =\operatorname{supp}^+d(E)\cup\operatorname{supp}^+d(D),
\]

and `d_o(E)>=g>0`, `d_o(D)=0` imply

\[
 \operatorname{supp}^+d(D)
 \subsetneq\operatorname{supp}^+d(H_\theta).
\]

This is the same sound one-time handoff proved by
`QuittingMinimumResponseChordLaw.response_support_ssubset_chord_of_killed`.
No endpoint-maximality or no-entry assumption is required for this direction.

Source regeneration needs more.  The checked constructor
`FinFourMinimumAtomProducer.regeneratedAtLawPoint` in
`Research/Quitting/FinFourProducerAtlas/MinimumResponseChordRegeneration.lean`
requires a *positive finite terminal-law atom* at the displayed minimum point.
The adjacent theorem as stated supplies no fixed terminal and no uniform mass
floor.  Even if every finite-rank endpoint is attached to some positive-atom
source, the atom labels can vary and their masses can tend to zero; the common
limit can have only all-Never mass.

The claimed regeneration is therefore valid only after adding, for example,

\[
 \exists S,\lambda>0,\quad
 \lambda\le\Pr_{D_{k+1}}(S)
 \quad\text{eventually}.
\]

Then `D` retains `S` with positive mass, every proper chord retains at least
`theta*lambda`, and `regeneratedAtLawPoint` gives both the killed-observer
endpoint source and the proper chord source with the incoming hard residual.
This is exactly the law input used by
`FinFourMinimumResponseChord.theta_mul_lambda_le_terminalMass` and
`regeneratedSources_same_source` in the checked rectangle setting.

The note should not say that the existing checked
`FinFourMinimumResponseRectangle` compiler directly applies to the adjacent
square: its public packet includes a literal one-mover horizontal edge and a
fixed positive response-law atom, neither of which is supplied by historical
label closure.  What applies is the generic chord geometry plus a new
adjacent-sequence adapter under the explicit hypotheses above.

## 5. Localization is sound but does not transport cap anchors

For a supplied nonobserver edit trace

\[
 H_{k,0}=P_k,\ldots,H_{k,L}=P_{k+1},
\]

the response differences telescope exactly.  If `L>=1`, some one-player
step has square charge at least `(g-epsilon_k)/L`.  The note correctly observes
that this does not make either response near-cap at the selected intermediate
edge.  In deficiency coordinates `A_j=a_j-b_j`, a positive rise can be caused
by either loss of old optimality or gain of new optimality.  No localization
of the sum controls either deficiency separately.

Add the harmless explicit condition `1 <= L`, or phrase the conclusion for a
nonempty trace.  If the endpoints have positive square charge then a
zero-length trace is impossible, but division by `L` should not be written
before that observation.

This section is an honest explanation of why the local checked rectangle is
not recovered from the adjacent diagonal square.

## 6. Regression audit

The Section 5 table realizes the claimed numbers.

* Players `0,1` quitting together at `t_k=2k+1` give prescribed payoff
  `(-1,-1,5,6)` and law `delta_{\{0,1\}}`.
* The unrestricted caps are `(0,0,6,6)`, so every diagonal endpoint has debt
  `(1,1,1,0)`.
* For observer `3`, quitting at `q_k=2k` gives singleton payoff `3`, while
  waiting past the pair gives `6`; hence each installed gain is `3` and the
  outgoing endpoint is exactly cap-attaining.
* At `P_k`, both `q_(k+1)` and `q_(k+2)` occur after the pair and have value
  `6`.  At `P_(k+1)`, `q_(k+1)` occurs before the pair and has value `3`, while
  `q_(k+2)` occurs after it and has value `6`.  Therefore `C_k=3`.
* The pure singleton `{2}` is an exact terminal Nash profile: player `2`
  obtains `3`, and every outsider weakly prefers not to join.  Thus `D_*=0`.

The regression validly shows that the displayed diagonal fields, even with
exact semantic/law equality and constant support, do not force fixed-law
premium or support descent.  Since the diagonal endpoints themselves already
form a constant semantic/law sequence, the sentence saying that "no
prescribed-payoff return is generated" is potentially misleading.  What the
example lacks is an **admissible chronological charged return** or a
Nash--Bellman path connecting those equal endpoints.  That narrower wording
matches the actual obstruction.

The regression does not test the missing positive-minimum provenance and is
correctly not presented as a Fin4 counterexample.

## 7. One-time versus renewable scope

The equality arm gives a real, source-attached strict inclusion from a proper
chord source to its killed-observer response source.  It does not compare that
support to the incoming source's support, preserve previously killed
coordinates through the next regenerated construction, or prove that another
application has a strictly smaller natural-valued rank.  Calling it a
"one-time support handoff" is accurate.

The strict arm is likewise a precise actual response family, but not an exact
punishment-floor edge or ordered charged return.  Neither arm consumes the
nonterminal strongly connected component in the maintained producer atlas.

## Required repair

The note should state the minimum-return result as a separate conditional
theorem with all of the following inputs:

1. the adjacent response-switch hypotheses and exact historical-label shifts;
2. joint semantic/law convergence of the next diagonal endpoints with total
   debt limit `D_*`;
3. one fixed finite terminal `S` and a positive eventual mass floor at those
   endpoints, if source regeneration is claimed; and
4. the incoming hard residual/minimum source from which
   `regeneratedAtLawPoint` is to inherit table-level data.

Its output is then exactly:

* an actual response-update family whose cross corner has a strictly
  off-minimum limit; or
* a minimum response chord, a strict
  `support(D) subsetneq support(H_theta)` handoff, and regenerated endpoint and
  chord sources.

The first output is not yet a consumer and the second is not renewable.  The
public Fin4 source still lacks the non-forgetful adjacent trace producing the
input.

## Export-gate verdict

**Do not export.**  After repair, the result remains a supplied-object
verifier plus a `D_*=0` insufficiency regression.  It has no current actual-data
adapter from arbitrary Fin4 source data and no downstream semantic consumer.
It therefore fails export criteria 4 and the strict-boundary requirement in
`exports/README.md`.  Retain it in `notes/` as the exact description of the
adjacent diagonal-square node and its missing renewable orientation.

