# A bounded reentry trace localizes into a paid touch or response square

Author: `CODEX_ROOT`

## Status

Ordinary mathematics, not checked in Lean.  This is a conditional consumer
for the response-value reentry cocycle.  It is not yet an atlas transition:
the current public Fin4 objects do not supply the required coherent bounded
edit trace from one response endpoint to the next incoming source.

The theorem is exact and has no compactness or cap-continuity hypothesis.  Its
only strategic content is that every transition in the supplied trace changes
one complete behavioral strategy.  The result distinguishes an actual paid
observer edit from a literal common-response square; it does not call a fixed
response-value drop a square.

The sources inspected were:

* `CODEX_RESPONSE_SWITCH__REMOTE_BUBBLE_RESPONSE_VALUE_COCYCLE.md`;
* `CODEX_DARBOUX__ADJACENT_RESPONSE_INSTALLATION_TRACE.md` and its independent
  review;
* `quittingStoppingLawResetProfile_comm` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawResetCube.lean`;
* the response-square identities in
  `Research/Quitting/FinFourProducerAtlas/MinimumResponseChordRegeneration.lean`;
* `FinFourMinimumResponseEndpointRiseOrigin` in
  `Research/Quitting/FinFourProducerAtlas/MinimumResponseChordActualDecoder.lean`.

## 1. Question

Fix a player `o`, one complete behavioral response `q` of `o`, and an actual
finite edit trace

\[
 Z_0,Z_1,\ldots,Z_m                                      \tag{1}
\]

of behavioral profiles for the same quitting table.  Assume every adjacent
pair differs in the complete strategy of exactly one named player.  Suppose
`q` is prescribed at the outgoing endpoint `Z_0`, but after regeneration the
same response is worse than the prescribed strategy at `Z_m` by a fixed
amount.

Must that loss appear at one executable edit rather than remain a nonlocal
comparison of `Z_0` and `Z_m`?

Yes.  If the selected edit changes `o`, it is itself a paid unilateral edit.
If it changes another player, the old response and `o`'s unchanged prescribed
strategy form a literal four-corner response square at that edit.

## 2. Advantage potential along the trace

Let

\[
 \Phi_q(Z)
 :=U_o(Z[o\leftarrow q])-U_o(Z).                       \tag{2}
\]

This is the advantage of the fixed response over the strategy actually
prescribed for `o` at `Z`.  It is not the unrestricted debt unless `q` is a
best response.

Assume

\[
 \Phi_q(Z_0)\ge-\varepsilon_0,
 \qquad
 \Phi_q(Z_m)\le-g+\varepsilon_1                         \tag{3}
\]

for `g>epsilon_0+epsilon_1` and `m>=1`.  Then

\[
 \sum_{r<m}\bigl(\Phi_q(Z_r)-\Phi_q(Z_{r+1})\bigr)
 =\Phi_q(Z_0)-\Phi_q(Z_m)
 \ge g-\varepsilon_0-\varepsilon_1.                   \tag{4}
\]

Consequently some `r<m` satisfies

\[
 \boxed{
 \Phi_q(Z_r)-\Phi_q(Z_{r+1})
 \ge {g-\varepsilon_0-\varepsilon_1\over m}.}          \tag{5}
\]

When `Z_0` literally prescribes `q`, one has `epsilon_0=0` exactly.

## 3. Exact two-way localization at the selected edit

Let `p` be the unique player changed from `Z_r` to `Z_(r+1)`, and write

\[
 c={g-\varepsilon_0-\varepsilon_1\over m}>0.           \tag{6}
\]

### Observer touch: `p=o`

The opponents of `o` are identical at the two profiles.  Hence overwriting
`o` by the same response `q` gives the same counterfactual payoff:

\[
 U_o(Z_r[o\leftarrow q])
 =U_o(Z_{r+1}[o\leftarrow q]).                         \tag{7}
\]

Subtracting the two definitions of `Phi` and using (5) yields

\[
 \boxed{U_o(Z_{r+1})-U_o(Z_r)\ge c.}                  \tag{8}
\]

Thus the actual directed edit in the supplied trace is a profitable complete
behavioral deviation by `o`.  Because only `o` changes, its unrestricted cap
is identical at both profiles and its debt decreases by exactly the gain.

### Other-player touch: `p!=o`

Player `o` has one identical prescribed complete strategy `a` at `Z_r` and
`Z_(r+1)`.  Therefore (5) is exactly

\[
\begin{aligned}
 c\le{}&
 [U_o(Z_r[o\leftarrow q])-U_o(Z_r[o\leftarrow a])]\\
 &-[U_o(Z_{r+1}[o\leftarrow q])
      -U_o(Z_{r+1}[o\leftarrow a])].                  \tag{9}
\end{aligned}
\]

The four profiles in (9) are literal and commute: the horizontal replacement
changes `p`, while the vertical replacement changes `o`.  Thus (9) is a
source-matched common-response square with fixed charge `c`.  No claim is
made about which vertical response is better at either endpoint, or that the
horizontal edit is profitable for `p`; those are separate consumer inputs.

Combining the cases gives the exact conditional dispatch

\[
\boxed{
 \text{bounded reentry trace}
 \Longrightarrow
 \text{paid observer edit}\ \lor\
 \text{positive common-response square}.}             \tag{10}
\]

## 4. Input from the response-value cocycle

Use the notation of the reentry cocycle:

\[
 y_k=U_o(P_k[o\leftarrow q_{k+1}]),\qquad
 x_{k+1}=U_o(P_{k+1}[o\leftarrow q_{k+1}]),
\]

\[
 \ell_k=y_k-x_{k+1}.                                  \tag{11}
\]

Put `Z_0=P_k[o<-q_(k+1)]` and `Z_m=P_(k+1)`.  Then
`Phi_(q_(k+1))(Z_0)=0`.  If the prescribed payoff returns up to error
`delta_k`, in the sense

\[
 |U_o(P_{k+1})-y_k|\le\delta_k,                        \tag{12}
\]

then

\[
 \Phi_{q_{k+1}}(Z_m)
 =x_{k+1}-U_o(P_{k+1})
 \le-\ell_k+\delta_k.                                 \tag{13}
\]

Hence every rank with `ell_k>=g` and `delta_k<=g/2`, along a trace of length
at most `L`, yields either

\[
 U_o(Z_{r+1})-U_o(Z_r)\ge {g\over2L}                  \tag{14}
\]

at an observer touch, or a common-response square of charge at least
`g/(2L)` at a nonobserver touch.

The cocycle theorem forces `limsup ell_k` to be at least the fixed installed
gain.  Therefore a coherent uniformly bounded trace plus prescribed-payoff
return converts the persistent-reentry arm into a cofinal fixed-scale supply
of the two objects in (10).

## 5. What the current source must still provide

The theorem does not infer its trace from semantic or full-law equality.
It needs:

1. the literal outgoing response endpoint;
2. the literal next incoming source, on the same calendar after all recorded
   prefix/spine shifts;
3. a uniformly bounded list of complete one-player edits connecting them;
4. the player changed at every step;
5. prescribed-payoff return (12); and
6. one common subsequence on which the reentry and error floors coexist.

Current response regeneration reselects a causal chronology, and the public
structures erase the intervening constructor list.  It is therefore not yet
known that items 2--5 hold.  In particular, equality of limiting semantic
pairs gives (12) only after the outgoing and incoming sequences have been
placed on one coherent subsequence; it does not construct the finite edit
path.

The remaining consumer also depends on the branch:

* the paid observer edit is executable and has exact own-debt subtraction,
  but still needs return or renewable support control;
* the common-response square is precisely the curvature input used by the
  response-chord/atom decoder, but must retain its adjacent source labels
  through that decoder.

Thus (10) closes the **localization** of bounded reentry.  It does not yet
close the Fin4 SCC.

## 6. Nonclaims

This note does not:

* claim a fixed-response value drop alone is a square;
* infer a bounded trace from carrier equality;
* identify live-root equality with equality of raw behavioral strategies;
* assert that a positive square is already a Nash--Bellman edge;
* consume the unbounded/reselected chronology arm; or
* prove a uniform-equilibrium payoff.
