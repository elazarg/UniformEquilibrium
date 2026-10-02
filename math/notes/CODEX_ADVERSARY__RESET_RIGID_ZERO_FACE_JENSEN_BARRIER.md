# Reset-rigid zero faces: the cap-Jensen barrier and two exact regressions

**Author:** `CODEX_ADVERSARY`  
**Date:** 2026-08-31  
**Status:** Propositions 2.1, 3.1, and 5.1 are proved ordinary mathematics.
The positive-minimum zero-preserving regeneration remains open.  The examples
are exact behavioral quitting games, not counterexamples to uniform
equilibrium and not export candidates.

## 1. Question and result

The reset-rigid chamber has a global minimum semantic point with a zero-debt
owner, a retained positive atom, conservative aggregate leakage, and a unique
strict all-Continue exact root at the returned cap.  The required missing
step is to replace a positive-debt coordinate while preserving every old zero
coordinate and returning to a source-faithful global minimum.

There is a precise obstruction before chronology enters:

> Purifying one player's stopping time commutes with prescribed payoff, but
> another player's unrestricted cap is a supremum of those conditional
> payoffs.  The supremum lies on the wrong side of the mixture identity.

I prove the exact cap-Jensen identity below.  A four-player regression then
shows that the new atom-preserving pure-time selector can be forced to destroy
another zero debt by a fixed amount, in both its finite-time and Never arms,
even though the source is a global debt minimum and the displayed cap has
unique strict all Continue.  A second four-player regression realizes an
actual same-law fixed-reset packet whose debt vector rotates from one simplex
vertex to another while retaining the moat, quantitative atom, strict toggle,
and unique cap root.  Its global minimum is zero elsewhere, isolating exactly
the full-carrier positive-minimum hypothesis which a successful proof must
use.

The strongest clean producer interface that survives is therefore not merely
an atom-preserving pure completion.  It is an atom-preserving pure completion
with vanishing **opponent cap-Jensen gaps**.

## 2. The exact cap-Jensen account

Fix an actual behavioral profile `sigma` and a player `o`.  Let `pi` be the
complete pure stopping-time law induced by `o`'s behavioral strategy, on

\[
 Q=\mathbb N\cup\{\mathsf{Never}\}.
\]

For `q in Q`, let `sigma[q]` replace only `o` by the pure stopping time `q`.
For every player `k`, write

\[
 U_k(q)=U_k(\sigma[q]),\qquad B_k(q)=B_k(\sigma[q]),
 \qquad d_k(q)=B_k(q)-U_k(q).                       \tag{2.1}
\]

### Proposition 2.1 (pure-time cap Jensen identity)

For the owner,

\[
 B_o(q)=B_o(\sigma)\quad(q\in Q),qquad
 \mathbb E_\pi d_o(q)=d_o(\sigma).                  \tag{2.2}
\]

For every `k != o`, define

\[
 J_k(\sigma,o)
 :=\mathbb E_\pi B_k(q)-B_k(\sigma).                \tag{2.3}
\]

Then

\[
 J_k(\sigma,o)\ge0,qquad
 \mathbb E_\pi d_k(q)=d_k(\sigma)+J_k(\sigma,o),    \tag{2.4}
\]

and consequently

\[
 \mathbb E_\pi D(\sigma[q])
 =D(\sigma)+\sum_{k\ne o}J_k(\sigma,o).             \tag{2.5}
\]

### Proof

Changing only `o` leaves `o`'s opponent profile and hence `B_o` unchanged.
The stopping-law mixture formula gives

\[
 U_k(\sigma)=\mathbb E_\pi U_k(q)                   \tag{2.6}
\]

for every coordinate.  For `k != o`, every fixed behavioral deviation
`tau_k` satisfies

\[
 U_k(\tau_k,\sigma_{-k})
 =\mathbb E_\pi U_k(\tau_k,\sigma[q]_{-k}).          \tag{2.7}
\]

Taking the supremum over `tau_k` before the expectation gives

\[
 B_k(\sigma)
 \le \mathbb E_\pi B_k(q),                          \tag{2.8}
\]

which is the nonnegativity of `J_k`.  Subtract (2.6) from (2.3) to obtain
(2.4), and sum the four identities to obtain (2.5). `QED`

This is the exact leakage quantity hidden by a purely owner-facing selector.
There is no reverse Jensen inequality: different pure completions may expose
different best responses of `k`.

## 3. A sufficient zero-face regeneration interface

Let `sigma_n` be source-attached profiles converging semantically to a global
minimum `w`, let `Z={k:d_k(w)=0}`, and suppose a fixed atom `S` has mass
tending to `m>0`.  Let `o in Z`, and decompose `o` into pure times as above.

### Proposition 3.1 (vanishing Jensen gaps suffice)

Assume

\[
 D(\sigma_n)\to D_*,\qquad
 \sum_{k\ne o}J_k(\sigma_n,o)\to0.                  \tag{3.1}
\]

Then there are pure completions `q_n` of `o` such that, for
`tau_n=sigma_n[q_n]`,

\[
 \liminf_n\Pr_{\tau_n}(S)\ge m,\qquad
 D(\tau_n)\to D_*,qquad
 d_k(\tau_n)\to0\quad(k\in Z).                     \tag{3.2}
\]

After compact extraction, every semantic target limit is a global minimum
and preserves the entire old zero set.  If replacement laws also converge,
the joint target supplies exactly the zero-preserving regeneration requested
by the reset chamber.

### Proof

Global minimality makes

\[
 C_n(q):=D(\sigma_n[q])-D_*+\sum_{k\in Z}d_k(\sigma_n[q])
\]

nonnegative.  Equations (2.2)--(2.5), convergence of `sigma_n` to `w`, and
(3.1) imply `E C_n -> 0`.  Combine this nonnegative cost with the atom
exposure in the elementary selector: choose `epsilon_n downarrow 0` with
`E C_n/epsilon_n -> 0`, restrict to `{C_n<=epsilon_n}`, and use that atom
exposure is bounded by one.  Some positive-support `q_n` has

\[
 C_n(q_n)\le\epsilon_n,qquad
 \Pr_{\sigma_n[q_n]}(S)
 \ge\Pr_{\sigma_n}(S)-\frac{\mathbb E C_n}{\epsilon_n}.
\]

These are (3.2).  Compactness and closed carrier membership give the final
statement. `QED`

Thus the smallest quantitative question is concrete:

\[
 \boxed{\text{Do reset rigidity and the positive-minimum moat force }
        \sum_{k\ne o}J_k\to0\text{ on one retained source?}}              \tag{3.3}
\]

The next example shows that global minimality, atom exposure, and unique cap
root do not force this at minimum debt zero.  Positivity must do real work if
(3.3) is true in the chamber.

## 4. Exact response regression with unique cap root

Use players `o=0`, `k=1`, anchor `a=2`, and passive player `b=3`.  At date
zero, `o` and `k` independently Quit with probability `1/2`; `a,b` Continue.
If both Continue, `a` Quits surely at date one.  Thus the law assigns mass
`1/4` to each of

\[
 \{o,k\},\quad\{o\},\quad\{k\},\quad\{a\}.          \tag{4.1}
\]

On these four outcomes put

\[
\begin{array}{c|rrrr}
 &\{o,k\}&\{o\}&\{k\}&\{a\}\\ \hline
 r_o&1&-1&2&-2\\
 r_k&1&-1&-1&1\\
 r_a&4&4&4&0\\
 r_b&4&4&4&4.
\end{array}                                         \tag{4.2}
\]

Complete the unused entries as follows.  For `o`, whenever a nonempty
opponent coalition `A` is fixed, set

\[
 r_o(A\cup\{o\})=r_o(A)-1,                           \tag{4.3}
\]

using the displayed values at `A={k}` and `A={a}` and arbitrary values at
the remaining opponent coalitions.  Set `r_o({o})=-1`.  Choose the unused
`k`-entries so that quitting alongside the date-one anchor pays at most `1`
(all of them may simply be made very negative).  For `a`, give every
nonempty coalition not containing `a` reward `4`, give its singleton reward
zero, and subtract one when `a` is inserted.  Do the same for `b`.

Direct backward induction gives

\[
 U=(0,0,3,4),\qquad B=(0,0,3,4),\qquad D=0.          \tag{4.4}
\]

For `o`, the two pure date-zero endpoints both pay zero against `k`'s
half-mixture.  For `k`, the Quit endpoint and the Continue-to-anchor endpoint
also both pay zero.  Player `a` gets `4` on the three early outcomes and zero
on its singleton, while no deviation improves the resulting value `3`.
Player `b` gets `4` surely and loses by inserting itself.

The exact root against the displayed cap `B` is uniquely all Continue:

- `o` strictly prefers Continue for every nonempty opponent coalition by
  (4.3), and against the empty coalition compares cap `0` with singleton
  reward `-1`;
- `a` and `b` have the same strict insertion loss and strict empty-coalition
  comparison; and
- once those three Continue, `k` compares cap `0` with singleton reward
  `-1` and also Continues strictly.

Now purify only `o`.

1. If `o` Quits at date zero, its own payoff and cap remain zero.  The atom
   `{o}` has mass `1/2`.  Player `k` still receives prescribed payoff zero,
   but pure Quit gives collision payoff `1`; hence `d_k=1`.
2. If `o` chooses Never, its own payoff and cap again remain zero.  The atom
   `{a}` has mass `1/2`.  Player `k` still receives prescribed payoff zero,
   but pure Continue obtains anchor payoff `1`; again `d_k=1`.

Thus `J_k=1`, while every other Jensen gap is zero.  Choosing `S={o}` forces
the bounded pure-time arm to lose the old zero; choosing `S={a}` forces the
Never arm to do the same.  The atom `{o}` also has the strict supported toggle

\[
 r_o(\{o\})=-1<0=r_o(\varnothing).                  \tag{4.5}
\]

The all-Never profile has zero debt, so (4.4) is genuinely a global minimum.
What is absent is the chamber's positive minimum.  This is an exact
counterexample to every zero-preservation claim that uses only pure-time
selection, atom mass, source global minimality, and uniqueness of the cap
root without exploiting `D_*>0`.

## 5. Exact same-law conservative reset rotation

The second regression targets the reset packet itself.  Again use four
players `0,1,2,3`; fix `epsilon=1/2`.  For player `1`, define on nonempty
coalitions not containing `1`

\[
 f_1(A)=
 \begin{cases}
 1,&2\in A,\\
 -1,&2\notin A,\ 0\in A,\\
 0,&\text{otherwise},
 \end{cases}                                        \tag{5.1}
\]

put `r_1({1})=-1`, and for nonempty `A` set

\[
 r_1(A\cup\{1\})=f_1(A)-\epsilon.                  \tag{5.2}
\]

Define player `2` symmetrically, interchanging `1` and `2`.  For players
`0,3`, put reward zero on every nonempty coalition not containing the player,
singleton reward `-1`, and reward `-epsilon` after insertion into a nonempty
coalition.

Consider the two actual profiles:

- `sigma^A`: player `1` Quits with probability `1/2` at date zero; after
  survival player `2` Quits surely at date one; if that row is bypassed,
  player `0` Quits surely at date two.
- `sigma^B`: interchange players `1` and `2` at dates zero and one; retain
  the same date-two player-`0` anchor.

Both profiles have the exact same law

\[
 \mu=\tfrac12\delta_{\{1\}}+\tfrac12\delta_{\{2\}},
 \qquad U(\sigma^A)=U(\sigma^B)=0.                  \tag{5.3}
\]

### Proposition 5.1 (literal reset rotation)

Their unrestricted cap and debt vectors are

\[
\begin{array}{c|c|c}
 &B&d\\ \hline
 \sigma^A&(0,1,0,0)&(0,1,0,0)\\
 \sigma^B&(0,0,1,0)&(0,0,1,0).
\end{array}                                         \tag{5.4}
\]

Taking source `sigma^A`, returned point `sigma^B`, reset owner `1`, and
incidence label `2`, every field of `QuittingFixedLawResetDispatch` is
realized literally, with the dynamic arm chosen to be all Continue.  In
particular,

\[
 d_1(\sigma^A)=1,qquad d_1(\sigma^B)=0,qquad
 \sum_{i\ne1}(d_i(\sigma^B)-d_i(\sigma^A))=1.       \tag{5.5}
\]

The old zero coordinate `2` becomes the unique positive coordinate.  Both
debt totals equal one, the law atom `{2}` has mass `1/2`, and member `2`
strictly gains one by leaving that singleton for Never.  At the returned cap,

\[
 B_i-r_i(\{i\})\ge1\quad(i=0,1,2,3),                \tag{5.6}
\]

and the owner average premium is exactly

\[
 U_1-r_1(\{1\})=1.                                  \tag{5.7}
\]

All Continue is the unique exact product root against either displayed cap.

### Proof

For player `1` in `sigma^A`, Continuing past date zero reaches player `2`'s
singleton payoff `1`; every insertion payoff is lower by `epsilon`, so its
cap is one.  In `sigma^B`, Continuing obtains `1` on the early player-`2`
half and `-1` on the surviving half, because bypassing its own date-one Quit
reaches the player-`0` anchor.  The value is zero, and no Quit plan improves
it.  Player `2` is symmetric.  Players `0,3` obtain zero by Continue and a
negative value from every Quit plan.  This proves (5.4).

Equations (5.3)--(5.5) verify joint same-law membership, reset, both debt
comparisons, and conservative transfer.  Positive incidence and the toggle
are carried by `{2}`.  Equations (5.6)--(5.7) are immediate from singleton
reward `-1` and (5.4).

For root uniqueness, condition on the opponents' current pure action
coalition `A`.  If `A` is nonempty, every player's Quit endpoint is exactly
`epsilon` below its Continue endpoint by construction.  If `A` is empty, the
Quit endpoint is singleton reward `-1`, strictly below the nonnegative cap
coordinate.  Hence Continue strictly dominates pointwise for every player,
and all Continue is the unique exact root.  Its semantic prefix is the
identity. `QED`

The all-Never profile has payoff and cap zero.  Therefore the actual global
minimum of this table is zero, not the level one in (5.4), and the table has a
uniform equilibrium.  The example is not a full reset-rigid counterexample.
Its exact content is narrower and sharp:

\[
\boxed{\text{same law + literal reset + conservative leakage + moat
 + quantitative toggle atom + unique cap root}}
\]

does not preserve old zeros.  A positive proof must use global comparison
against profiles outside this law fibre, not only the checked reset packet or
finite `Fin 4` debt-simplex geometry.

## 6. Consequences for the named atom sources

The nonsingleton anti-diffusion estimate supplies a literal quantitative row;
the singleton clock compression supplies a one-date owner replacement with
the owner cap unchanged; and the pure-time selector aligns arbitrary atom
exposure with the owner's near-cap payoff.  None controls (2.3).  The first
regression shows that even exact owner cap preservation and increased atom
mass can coexist with a unit opponent Jensen gap.  The second shows that the
fixed-law reset can realize the corresponding debt rotation without any
slack in its transfer account.

Unique strict all Continue at `B(y)` does not repair the issue because the
conditional profiles `sigma[q]` are evaluated against their own opponents
and tails.  Root uniqueness at the one displayed cap supplies no common best
response for an old zero coordinate across those conditional profiles.

## 7. Proved versus unproved

### Proved here

- the exact cap-Jensen identities (2.2)--(2.5);
- the vanishing-Jensen sufficient regeneration criterion, including atom
  retention and all old zeros;
- an exact global-minimum-zero Fin4 regression defeating zero preservation in
  both pure-time timing arms while retaining a unique strict cap root; and
- an exact same-law Fin4 reset packet with conservative vertex-to-vertex debt
  rotation, quantitative strict-toggle atom, moat, and unique cap root.

### Not proved

- that the actual positive-minimum reset-rigid source has vanishing Jensen
  gaps;
- that atom compression or anti-diffusion bounds any opponent cap-Jensen gap;
- replacement-law convergence back to the original law-tight face; or
- any uniform-equilibrium conclusion from the chamber.

## 8. Exact declarations inspected

- `QuittingFixedLawResetDispatch` and
  `QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch` in
  `TerminalSemanticResetIncidenceCapReturn.lean`;
- `QuittingLawTightResetRigidChamber` and
  `exists_quittingLawTightResetRigidChamber` in
  `LawTightCapNashStrictMinimum.lean`;
- `QuittingReprojectionDiffuseWindowPacket.terminal_card_eq_one` and the
  preceding stage-mass power estimates in
  `TerminalSemanticNonsingletonAntiDiffusion.lean`;
- `FinFourOwnerCompressedSingletonEndpoint.targetProfile_ownerCap_eq`,
  `FinFourMinimumAtomChronology.nonempty_ownerCompressedSingleton`, and
  `FinFourMinimumAtomProducer.exists_commonChronology_cofinal_ownerCompressedSingleton`
  in `Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`;
- `minimumTerminalSemantic_singletonMargin` in
  `TerminalSemanticAuxiliaryNashBudget.lean`; and
- the pure-time extremality and stopping-law mixture declarations cited in
  `CODEX_ROOT__ZERO_DEBT_ATOM_PRESERVING_PURE_TIME_SELECTOR.md`.

## 9. Concrete next question

For the actual positive-minimum source approximants, can the strict moat and
the common cap-root stack prove either

\[
 \sum_{k\ne o}J_k(\sigma_n,o)\longrightarrow0,       \tag{9.1}
\]

or a charged lower bound which debits every nonvanishing Jensen gap from the
finite exact-block capacity?  The coordination regression says that neither
atom mass nor unique root alone can prove (9.1); a successful argument must
couple the conditional best replies to the retained cap-root chronology.
