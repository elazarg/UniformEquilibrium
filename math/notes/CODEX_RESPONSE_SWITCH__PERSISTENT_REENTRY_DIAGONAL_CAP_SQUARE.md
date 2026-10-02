# Persistent reentry yields a diagonal cap square, not yet renewable descent

Author: `CODEX_RESPONSE_SWITCH`

## Status

Ordinary mathematics, not checked in Lean.  Internal Research note; no
export claim.

Persistent response-value reentry loss can be strengthened to a conditional
version of option (i) in the question: two consecutive response switches form
an exact payoff square whose two diagonal response endpoints are approximately
cap-attaining and source-attached.  The square charge is at least the next
switch gain minus the preceding endpoint error.  It is a literal commuting
profile square when the supplied transition between the two base environments
does not edit the observer (after making the source chronology's clock shifts
explicit).

This does not yet give a checked consumer.  The horizontal side joins two
successive regenerated environments and can change several players.  The
current response-chord compiler requires one literal mover replacement.
Localizing the square along a bounded edit trace preserves charge on one
one-player sub-square, but generally loses cap-attainment at that local
sub-square's endpoints.

If the next diagonal endpoints are additionally known to converge to the
minimum fibre and retain one fixed positive finite-law atom, compactifying
the reactivated cross corner gives an exact additional dichotomy: its limit
is strictly off minimum and the actual near-cap response family approaches
the next minimum endpoint, or it is itself minimum and generic
response-chord geometry yields a genuine source-attached killed-observer
support handoff.
The latter handoff is one-time, not yet renewable relative to the incoming
source; the former edge is not yet an admissible chronological return.

The rational ordered-clock regression from
`CODEX_RESPONSE_SWITCH__REMOTE_BUBBLE_RESPONSE_VALUE_COCYCLE.md` realizes the
new diagonal square at fixed charge with both diagonal endpoints having
exactly the same semantic pair and full terminal law.  Its support is
constant and its fixed-law premium is zero.  Thus the new square is real but
not locally consumable from its displayed fields.  The regression has
`D_*=0`; positive-minimum source provenance remains the only possible source
of a renewable orientation.

## 1. Exact adjacent diagonal-square theorem

Fix one observer `o`.  Let `P_k` be actual profiles and let `q_k` be
pure-time responses, already expressed in one common absolute clock (or after
the exact prefix shifts required by the source chronology).  Put

\[
 V_k(q):=U_o(P_k[o\leftarrow Q_q]).                    \tag{1.1}
\]

Assume for every `k`:

1. the installed old/new switch has a fixed gain

   \[
   V_k(q_{k+1})-V_k(q_k)\ge g>0;                       \tag{1.2}
   \]

2. its outgoing response endpoint is approximately cap-attaining,

   \[
   d_o(P_k[o\leftarrow Q_{q_{k+1}}])\le\varepsilon_k,  \tag{1.3}
   \]

   with `epsilon_k->0`; and
3. `q_(k+1)` is literally the incoming response label at the next displayed
   occurrence of this same observer.

Since changing `o`'s prescribed strategy leaves its unrestricted cap fixed,
(1.3) says

\[
 B_o(P_k)-V_k(q_{k+1})\le\varepsilon_k.                \tag{1.4}
\]

Every response payoff is at most that cap.  In particular,

\[
 V_k(q_{k+2})-V_k(q_{k+1})\le\varepsilon_k.            \tag{1.5}
\]

At the next environment, (1.2) gives

\[
 V_{k+1}(q_{k+2})-V_{k+1}(q_{k+1})\ge g.               \tag{1.6}
\]

Subtracting (1.5) from (1.6) produces the diagonal-square charge

\[
\boxed{
\begin{aligned}
 C_k:={}&
 [V_{k+1}(q_{k+2})-V_{k+1}(q_{k+1})]\\
 &-[V_k(q_{k+2})-V_k(q_{k+1})]
 \ge g-\varepsilon_k.
\end{aligned}}                                         \tag{1.7}
\]

The lower diagonal endpoint

\[
 D_k=P_k[o\leftarrow Q_{q_{k+1}}]
\]

has `o`-debt at most `epsilon_k`, and the upper diagonal endpoint

\[
 D_{k+1}=P_{k+1}[o\leftarrow Q_{q_{k+2}}]
\]

has `o`-debt at most `epsilon_(k+1)`.  Both are actual profiles and retain
their respective incoming source attachments.  The vertical response
replacements commute with a supplied horizontal transformation only when that
transformation does not edit `o`.  Without this extra source-level condition,
(1.7) remains an exact four-payoff identity but is not claimed to be a literal
commuting profile square.

This conclusion does not need the sign of the reentry loss.  In terms of the
same-label reentry losses

\[
 \ell_k(q)
 :=V_k(q)-V_{k+1}(q),                                  \tag{1.8}
\]

the square has the exact curvature identity

\[
 \boxed{C_k=\ell_k(q_{k+1})-\ell_k(q_{k+2}).}           \tag{1.9}
\]

Thus a persistent loss of the installed response necessarily separates it
from the next cap response by a fixed reentry-curvature square.

### 1.1 The reactivated cross corner has an exact minimum-return dichotomy

The next environment already contains a stronger one-sided object.  Put

\[
 E_k=P_{k+1}[o\leftarrow Q_{q_{k+1}}],
 \qquad
 D_{k+1}=P_{k+1}[o\leftarrow Q_{q_{k+2}}].             \tag{1.10}
\]

These profiles have literally the same opponents.  Hence their unrestricted
`o`-caps agree, and

\[
 d_o(E_k)-d_o(D_{k+1})
 =U_o(D_{k+1})-U_o(E_k)
 =V_{k+1}(q_{k+2})-V_{k+1}(q_{k+1})
 \ge g.                                                \tag{1.11}
\]

Thus the update from the reactivated cross corner to the next diagonal
endpoint is not merely a paid row: it is the displayed complete behavioral
near-cap response, and it kills at least `g` of the observer's debt (up to
the endpoint's vanishing error).

Once the adjacent historical response label is retained, `E_k` is an actual
source-indexed profile sequence.  Compactness then supplies, after refining
that same source subsequence, a joint semantic/law cluster point `E`.  Assume
separately that the displayed diagonal endpoints converge jointly to `D`,
with

\[
 D(D)=D_*,\qquad d_o(D)=0.                             \tag{1.12}
\]

If source regeneration is claimed, assume moreover that one fixed finite
terminal `S` and one `lambda>0` satisfy

\[
 \lambda\le\Pr_{D_{k+1}}(S)\quad\text{eventually}.    \tag{1.12a}
\]

Neither the minimum identity in (1.12) nor the atom floor (1.12a) follows
from historical-label retention and compactness alone.

Then global minimality and (1.11) give the exact alternative

\[
\boxed{
\begin{array}{ll}
D(E)>D_*:&
  \begin{array}{l}
  \text{an actual fixed-gain response family whose two displayed limits are}\
  \text{respectively off minimum and minimum;}
  \end{array}\\[2mm]
D(E)=D_*:&
  \text{a proper minimum response chord }E\leadsto D
  \text{ with }d_o(E)\ge g\text{ and }d_o(D)=0.
\end{array}}                                           \tag{1.13}
\]

In the equality arm, every proper stopping-law mixture of the two observer
strategies is again on the minimum fibre.  Its debt support is the union of
the endpoint supports, and its law retains a positive fraction of every fixed
positive atom carried by `D`.  The generic minimum-response-chord geometry
therefore gives the strict inclusion

\[
 \operatorname{supp}^+d(D)
 \subsetneq
 \operatorname{supp}^+d(H_\theta)                    \tag{1.14}
\]

for every proper chord point `H_theta`.  This is a genuine one-time
support handoff at the level of the actual response family and its joint
limits.  Turning it into the checked Fin4 regenerated-source object still
requires a new adjacent-family adapter: the present Fin4 compiler expects a
one-mover horizontal edge together with its retained atom, while the adjacent
construction supplies neither from its current fields.  Even after that
adapter, the handoff is not yet renewable relative to the *incoming* source:
the next forced-pair construction may introduce a previously absent debtor
before its next response is applied.

In the strict arm, (1.11) is stronger than an anonymous local gain but is
still not a checked chronological return.  It gives actual finite response
profiles whose joint limits lie respectively off and on the minimum fibre;
it does not give an actual edge between two attained limiting profiles.  The
response changes the terminal law, and the present return compilers require a
Nash--Bellman edge or an ordered charged path.  No theorem currently turns
this law-changing response family into either object.

The public adjacent source does not currently retain the historical response
label through the next source chronology, so it cannot even define the
source-indexed `E_k`.  Retaining that label makes `E_k` and a compact cluster
point `E` available, but it does not supply the separate minimum convergence
(1.12), atom floor (1.12a), or the adjacent-family regeneration adapter.  Thus
(1.13) is conditional geometry for a strengthened non-forgetful cross-corner
source, not an unconditional consumer of the current Fin4 packet.

## 2. First-disagreement chronology remains exact

In the strict clock arm, the incoming and outgoing labels at `P_(k+1)` obey

\[
 q_{k+1}<t_{k+1}\le q_{k+2}.                           \tag{2.1}
\]

Their first disagreement is therefore exactly `q_(k+1)`.  A fixed gain in
(1.6) gives the same opponent-survival floor as in the remote-bubble note.
The four corners in (1.7) retain both named responses, both actual base
profiles, and this first-disagreement date.

At the preceding base `P_k`, the same two responses need not have their first
disagreement at its marked date in a useful literal sense.  Their strategies
can differ again after certain absorption.  Equation (1.7) is a payoff square
of complete pure-time deviations; it is not silently replaced by a literal
one-date square.

## 3. Localization along a supplied regeneration trace

Suppose the actual transition from `P_k` to `P_(k+1)` is supplied as

\[
 H_{k,0}=P_k,
 H_{k,1},\ldots,H_{k,L}=P_{k+1},                       \tag{3.1}
\]

where `L>=1`, each step changes one player other than `o`, and `L` is uniformly
bounded.  Because the two response replacements commute literally with
every horizontal step, define

\[
 A_{k,j}:=
 U_o(H_{k,j}[o\leftarrow Q_{q_{k+2}}])
 -U_o(H_{k,j}[o\leftarrow Q_{q_{k+1}}]).               \tag{3.2}
\]

Then

\[
 C_k=A_{k,L}-A_{k,0}
     =\sum_{j<L}(A_{k,j+1}-A_{k,j}).                   \tag{3.3}
\]

Consequently some literal one-player step carries a commuting response
square of charge at least

\[
 \frac{g-\varepsilon_k}{L}.                            \tag{3.4}
\]

This is a genuine source-matched four-corner square, not an anonymous paid
row.  It retains the changed player, the observer, both response labels, and
the actual consecutive profiles in the regeneration trace.

The cap anchors, however, occur only at opposite ends of the whole path:
`q_(k+1)` is near-cap at `H_(k,0)` and `q_(k+2)` is near-cap at `H_(k,L)`.
Nothing in (3.3) makes either response near-cap at the selected intermediate
edge.  Thus the localized square does not instantiate
`FinFourMinimumResponseRectangleSequence`, whose receiving response endpoint
must have vanishing observer debt on that same literal mover edge.

The same obstruction can be written in cap-deficiency coordinates.  Put

\[
 a_j=B_o(H_{k,j})-
   U_o(H_{k,j}[o\leftarrow Q_{q_{k+1}}]),
 \qquad
 b_j=B_o(H_{k,j})-
   U_o(H_{k,j}[o\leftarrow Q_{q_{k+2}}]).              \tag{3.5}
\]

Then `a_0<=epsilon_k`, `b_L<=epsilon_(k+1)`, and

\[
 A_{k,j}=a_j-b_j.                                      \tag{3.6}
\]

A fixed rise of `A_(k,j)` can be caused by loss of optimality of the old
response, acquisition of optimality of the new response, or both.  It need
not occur at an edge where either deficiency is small.

## 4. Fixed-law and support-rank audit

Assume now that the finite-rank actual debts of the two diagonal endpoint
families tend to `D_*`, and that their joint semantic/law cluster points lie
on the positive global minimum fibre.  This is the form actually intended in
source-faithful response regeneration; the finite profiles themselves need
not have debt exactly `D_*`.

### Fixed law

Even equality of their complete terminal laws does not make (1.7) a feasible
fixed-law variation.  The off-diagonal response profiles

\[
 P_k[o\leftarrow Q_{q_{k+2}}],
 \qquad
 P_{k+1}[o\leftarrow Q_{q_{k+1}}]
\]

can have different laws.  The fixed-law reset minimizer prices only actual
points on one retained-law slice; it supplies no variational inequality for
this cap-changing off-diagonal square.

### Support rank

Both diagonal endpoints have vanishing `o`-debt.  This preserves one killed
coordinate at the displayed endpoints, but it does not accumulate new
zeros.  The other three unrestricted caps can change under the horizontal
regeneration.  Hence

\[
 \operatorname{supp}^+d(D_k)
 \quad\text{and}\quad
 \operatorname{supp}^+d(D_{k+1})
\]

may have the same cardinality with different members.  The existing strict
support theorem needs no support entry (or endpoint maximality plus its
proper minimum chord).  Neither follows from (1.7).

The within-origin `FinFourMinimumResponseRectangle` is stronger in a
different direction: its horizontal side is one fixed mover replacement, its
upper response endpoint is minimum, and its proper executable response chord
is available.  The adjacent square (1.7) has two cap-attaining diagonal
endpoints but a multi-edit horizontal side.  Current APIs do not combine
those complementary strengths.

## 5. Exact regression: the stronger square can still circulate

Use the rational table and profiles from
`CODEX_RESPONSE_SWITCH__REMOTE_BUBBLE_RESPONSE_VALUE_COCYCLE.md`, Section 4.
The fixed observer is `3`,

\[
 q_k=2k,
 \qquad t_k=2k+1,
\]

and players `0,1` Quit together at `t_k` while players `2,3` prescribe Never
in `P_k`.  The response endpoint

\[
 D_k=P_k[3\leftarrow Q_{q_{k+1}}]
\]

terminates with `{0,1}` before `q_(k+1)`, has marked mass one, and has exact
observer debt zero.

At `P_k`, both `q_(k+1)` and `q_(k+2)` occur after the pair, so

\[
 V_k(q_{k+1})=V_k(q_{k+2})=6.                          \tag{5.1}
\]

At `P_(k+1)`, `q_(k+1)` occurs before the new pair date while `q_(k+2)`
occurs after it, so

\[
 V_{k+1}(q_{k+1})=3,
 \qquad
 V_{k+1}(q_{k+2})=6.                                   \tag{5.2}
\]

Therefore

\[
 \boxed{C_k=(6-3)-(6-6)=3}                             \tag{5.3}
\]

and both correct diagonal endpoints are exactly cap-attaining.

Nevertheless every `D_k` has the identical unrestricted terminal semantic
pair and full law

\[
 d(D_k)=(1,1,1,0),
 \qquad
 \operatorname{Law}(D_k)=\delta_{\{0,1\}}.             \tag{5.4}
\]

Thus the positive-debt support is constant, the diagonal fixed-law premium
is zero, and no admissible chronological charged return is generated by the
square.  The
off-diagonal lower-right profile at `P_(k+1)[3<-q_(k+1)]` has the response
value `3`; its law differs from the diagonal bubble law, exactly where a
fixed-law argument loses feasibility.

The table has an exact singleton equilibrium `{2}`, so `D_*=0`.  This does
not refute a theorem genuinely using positive minimum.  It proves that the
diagonal cap-square data, exact semantic/law equality, and constant support
do not themselves yield fixed-law premium, support descent, or terminal
approximation along the displayed chain.

## 6. Relation to the anchored Jensen ledger

The square (1.7) has the same algebraic orientation as Alternative B of
`CODEX_JOULE__JENSEN_ACTIVE_PASSPORT_DICHOTOMY.md`, but a different
co-realization profile.

* The Jensen theorem has a literal one-owner horizontal mixture and a
  response square on two supported owner-clock components.  Its two correct
  response endpoints are near-cap, but the receiving component need not be
  mass-good or near-minimum.
* The adjacent theorem has two source-attached near-cap diagonal endpoints
  carrying the chronological response chain.  Its horizontal transition is
  the whole regeneration and need not be one-owner or one-step.

Combining the two requires identifying the adjacent regeneration with one
supported component pair of an anchored disintegration, or transporting the
adjacent cap anchors to the one-step square selected by (3.3).  Neither
identification is supplied by the current public objects.

## 7. Public-source verdict and exact next interface

The current public source does **not** supply the hypotheses of the adjacent
theorem as one object.

* `FinFourMinimumResponseRectangle` carries one current observer response and
  one current mover edge, but no historical incoming response from the
  preceding regenerated endpoint.
* `responseSource` regenerates a minimum source at the current response point,
  but its chronology is reselected and does not expose the literal next
  endpoint profile as an edit path from the preceding response endpoint.
* The ordinary-mathematics
  `CODEX_DARBOUX__ADJACENT_RESPONSE_INSTALLATION_TRACE.md` specifies the
  missing non-forgetful trace, including exact clock shifts and the first
  observer-touch split; that wrapper is not a checked public producer.

If the traced source adapter is built, the strongest honest next structure is

```text
FinFourAdjacentDiagonalResponseSquare
```

carrying:

* one fixed observer and three consecutive shifted response labels;
* the two actual regenerated base environments;
* the two cap-attaining diagonal response endpoints;
* the fixed square charge (1.7);
* the bounded literal nonobserver edit trace, if available; and
* the incoming minimum, marked-law, and source passports.

A complete consumer still needs one genuinely new assertion:

\[
\boxed{
\begin{array}{c}
\text{cap-attaining diagonal response square on the positive minimum fibre}\\
\Longrightarrow\\
\text{a local cap-attaining mover square, fixed-law entrance,}\\
\text{or no-entry renewable support descent.}
\end{array}}                                            \tag{7.1}
\]

The regression shows why “same diagonal law” cannot replace any of the three
conclusions.

## 8. Nonclaims

This note does not:

* construct the adjacent trace from current public Fin4 data;
* claim the raw pure-time square is a literal one-date square;
* preserve cap-attainment when localizing through arbitrary intermediate
  edits;
* derive a fixed-law premium from diagonal law equality;
* prove no support entry or renewable rank; or
* prove or refute Fin4 uniform equilibrium.

## 9. Files and declarations inspected

* `Research/Quitting/FinFourProducerAtlas/MinimumResponseChordActualDecoder.lean`:
  the literal four-corner decoder and retained source subsequence.
* `Research/Quitting/FinFourProducerAtlas/MinimumResponseChordRegeneration.lean`:
  `FinFourMinimumResponseRectangle`, `FinFourMinimumResponseChord`,
  `debt_eq_affine`, `support_eq_union`,
  `response_support_ssubset_chord_of_killed`, and the regenerated sources.
* `Research/Quitting/MinimumResponseChordLaw.lean`:
  executable response chords, law affinity, minimum-fibre debt affinity, and
  support union/strictness.
* `notes/CODEX_LEIBNIZ__SOURCE_FAITHFUL_RESPONSE_CHORD_COCYCLE_BOUNDARY.md`:
  the exact local response potential, four-corner compactification boundary,
  and persistent-zero target.
* `notes/CODEX_DARBOUX__ADJACENT_RESPONSE_INSTALLATION_TRACE.md`:
  the non-forgetful response installation trace and first-observer-touch
  boundary.
* `notes/CODEX_JOULE__JENSEN_ACTIVE_PASSPORT_DICHOTOMY.md`:
  anchored Jensen component selection and its missing mass/minimum
  co-realization.
* `notes/CODEX_RESPONSE_SWITCH__REMOTE_BUBBLE_RESPONSE_VALUE_COCYCLE.md` and
  `notes/CODEX_RIEMANN__REMOTE_BUBBLE_ALL_NEVER_JUMP_REGRESSION.md`:
  ordered-clock cocycle and exact zero-minimum regression.
