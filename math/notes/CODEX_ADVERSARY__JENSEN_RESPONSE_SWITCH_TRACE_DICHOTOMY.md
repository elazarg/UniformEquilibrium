# A positive cap-Jensen gap forces a source-visible response switch

**Author:** `CODEX_ADVERSARY`  
**Date:** 2026-08-31  
**Status:** Corrected after the independent review
[`JENSEN_REVIEW`](../feedback/CODEX_ADVERSARY__JENSEN_RESPONSE_SWITCH_TRACE_DICHOTOMY__BY_JENSEN_REVIEW.md).
Theorem 3.1, Corollaries 3.2--3.3, and the regression in Section 6 are proved
ordinary mathematics, not checked in Lean.  The theorem is source-faithful
at the level of one actual profile and its stopping-law disintegration.  Its
escaping arm reaches an essential-Never/player-deleted obstruction only in
a compact stopping-law limit, not in the per-rank finite-splice modulus.  No
uniform equilibrium or reset-rigid chamber elimination is claimed.  This is
an internal research note and is **not export-worthy** for the reasons in
Section 9.

This note continues
[`CODEX_ADVERSARY__RESET_RIGID_ZERO_FACE_JENSEN_BARRIER.md`](CODEX_ADVERSARY__RESET_RIGID_ZERO_FACE_JENSEN_BARRIER.md)
and uses the trace estimate from
[`CODEX_STRENGTHEN__CAP_SWITCHING_DELETED_BUBBLE_AND_REPLAY_CONTRACT.md`](CODEX_STRENGTHEN__CAP_SWITCHING_DELETED_BUBBLE_AND_REPLAY_CONTRACT.md).

## 1. Exact question and answer

Let `sigma` be one actual finite-player quitting profile, let `o` be a player,
and disintegrate `o`'s complete behavioral stopping law `pi` into pure times

\[
 Q=\mathbb N\cup\{\mathsf{Never}\}.
\]

Write `sigma[t]` for the actual profile obtained by replacing only `o` by
pure time `t`.  For an outsider `i != o`, let

\[
 J_i=\mathbb E_{t\sim\pi}B_i(\sigma[t])-B_i(\sigma)\ge0. \tag{1.1}
\]

The question is whether `J_i >= eta > 0` has a genuinely source-attached
output, rather than only an arbitrary paid first-disagreement row on one
possibly rare component.

The answer is yes, up to the known deleted-clock boundary.  There are two
supported owner clocks and two approximately optimal pure responses whose
commuting rectangle has fixed size.  They can be selected so that, at their
first disagreement date `r`, simultaneously

1. the original owner law survives to `r` with fixed probability;
2. the players other than the owner and observer survive to `r` with fixed
   probability at the original source; and
3. one receiving response edge is a fixed-gain paid row with vanishing
   observer debt at its high endpoint.

Consequently the original source has a fixed full-opponent survival floor at
`r`.  At every rank, regardless of the size of `r`, the paid row enters the
checked paid-cap trichotomy once the positive global minimum is supplied; its
source structure has no bounded-date hypothesis.  A subsequence additionally
makes `r` either fixed or divergent.  The divergent arm gives a positive
all-Never atom for the observer's opponents in a compact stopping-law limit.
That is an essential-Never times pair-deleted-survival obstruction at the
limit, but it need not give a positive finite-splice boundary product at any
finite rank.  Section 6 gives an exact same-table regression for that last
failed implication.

If one actual profile has `d_o(sigma)=0`, both selected positive-support clock
components retain owner debt zero.  The paid-cap source is based at the
unmodified receiving component `sigma[a]`, not at the high-response endpoint,
so exact cap-Nash debt scaling preserves this zero through every prefix and
at the port limit.  The actual reset-rigid adapter generally supplies only
`d_o(sigma_n)->0`, not rankwise equality.  Corollary 3.3 repairs that case:
the two selected components and every associated port have owner debt tending
to zero, with all response and survival constants unchanged.

## 2. The response rectangle

Fix a reward bound `M>0`, so every terminal payoff lies in `[-M,M]`, and fix
`epsilon>0`.  For every supported `t`, choose a pure time `q_t` satisfying

\[
 V_t(q_t)\ge B_i(\sigma[t])-\varepsilon,
 \qquad
 V_t(q):=U_i(\sigma[t][i\leftarrow Q_q]).           \tag{2.1}
\]

Pure-time extremality makes this legitimate for the unrestricted behavioral
cap; `Never` is included.  For two independent clocks `T,S` with law `pi`,
put

\[
 A(t,s)=V_t(q_t)-V_t(q_s),                           \tag{2.2}
\]

and define the symmetric response rectangle

\[
 R(t,s)=A(t,s)+A(s,t).                               \tag{2.3}
\]

Fixed-response affinity in the owner stopping-law mixture gives

\[
 \begin{aligned}
 \mathbb E A(T,S)
 &=\mathbb E_TV_T(q_T)-\mathbb E_S\mathbb E_TV_T(q_S)\\
 &\ge \mathbb E_TB_i(\sigma[T])-\varepsilon-B_i(\sigma)\\
 &=J_i-\varepsilon.
 \end{aligned}                                      \tag{2.4}
\]

By symmetry,

\[
 \boxed{\mathbb E R(T,S)\ge2(J_i-\varepsilon).}     \tag{2.5}
\]

Also `A(t,s)>=-epsilon`, because `q_t` is approximately optimal at its own
component, and `|R(t,s)|<=4M`.

If `q_t != q_s`, let `r(t,s)` be their finite first disagreement.  Define the
source owner's survival tail

\[
 p(r)=\pi\{t:t\ge r\},                              \tag{2.6}
\]

where `Never>=r` for every finite `r`.  If `q_t=q_s`, then `R(t,s)=0`.  If
both owner clocks satisfy `t<r(t,s)` and `s<r(t,s)`, the owner absorbs in
each component before the two observer responses disagree, so again

\[
 R(t,s)=0.                                          \tag{2.7}
\]

This elementary screening observation is what lets the Jensen expectation
retain part of the *original* owner tail.

## 3. Tail-aware response-switch theorem

### Lemma 3.0 (tail quantile bound)

For every `0<c<=1`,

\[
 \pi\{t:p(t)<c\}\le c.                              \tag{3.1}
\]

Indeed, the set on the left is an upper tail in the ordered space
`Nat union {Never}`.  If it has a least finite point `t_0`, its mass is at
most `p(t_0)<c`; if it consists only of `Never`, its mass is
`pi({Never})<c`.

### Theorem 3.1 (positive Jensen gap gives a source-visible switch)

Assume

\[
 J_i\ge\eta>0                                      \tag{3.2}
\]

and choose `0<epsilon<=eta/4` in (2.1).  Then there are supported owner clocks
`a,b`, two distinct response times `q_a,q_b`, and their first disagreement
date `r` such that

\[
 R(a,b)\ge\eta/2,                                  \tag{3.3}
\]

\[
 p(r)\ge\eta/(16M),                                \tag{3.4}
\]

and, after possibly interchanging `a,b`,

\[
 V_a(q_a)-V_a(q_b)\ge\eta/4.                       \tag{3.5}
\]

The receiving owner clock satisfies `a>=r` (with `Never` above every finite
date).

The high response is approximately cap attaining at the receiving component:

\[
 d_i(\sigma[a][i\leftarrow Q_{q_a}])\le\varepsilon. \tag{3.6}
\]

Let

\[
 H_{-i,-o}(\sigma,r)
 =\Pr_\sigma(\text{every player other than }i,o
             \text{ survives to }r).
\]

Then

\[
 H_{-i,-o}(\sigma,r)\ge\eta/(8M),                  \tag{3.7}
\]

and hence the original source satisfies the full observer-opponent bound

\[
 \Pr_\sigma(\text{every player other than }i
             \text{ survives to }r)
 \ge {\eta^2\over128M^2}.                           \tag{3.8}
\]

Finally, the receiving edge (3.5) gives a literal
`QuittingPaidFirstDisagreementRow` of gain `eta/4`, whose full live mass is
at least `eta/(8M)`.

#### Proof

Put `c=eta/(16M)`.  A positive Jensen gap implies `eta<=2M`, so `c<=1`.
Suppose there were no pair satisfying both (3.3) and (3.4).  By (2.7), on
the event `p(r)<c` and `R!=0`, at least one sampled owner clock is at least
`r`.  On that event at least one of `p(T),p(S)` is below `c`.  Lemma 3.0 and
the union bound therefore give

\[
 \Pr(p(r)<c,\ R\ne0)\le2c.                          \tag{3.9}
\]

Since `|R|<=4M`, the alleged absence of a simultaneous pair would imply

\[
 \mathbb E R\le \eta/2+4M(2c)=\eta.                \tag{3.10}
\]

But (2.5) and `epsilon<=eta/4` give

\[
 \mathbb E R\ge3\eta/2,                            \tag{3.11}
\]

a contradiction.  Thus (3.3)--(3.4) hold for one supported pair.  One of
`A(a,b),A(b,a)` is at least `R(a,b)/2`, proving (3.5) after orientation.
If `a<r`, the owner would absorb before the two observer responses disagree,
making the left side of (3.5) zero; hence `a>=r`.  Equation (3.6) is (2.1)
at the receiving component.

For the two fixed observer responses, define

\[
 G(P)=V_P(q_a)-V_P(q_b).
\]

The profiles `sigma[a]` and `sigma[b]` differ only in owner `o`'s complete
stopping law.  The one-edge trace-friction estimate, with replacement
amplitude one, gives

\[
 |G(\sigma[a])-G(\sigma[b])|
 \le4M H_{-i,-o}(\sigma,r).                         \tag{3.12}
\]

The deleted survival is exactly the same at `sigma`, `sigma[a]`, and
`sigma[b]`, because it omits both changed players.  The left side of (3.12)
is `R(a,b)`, so (3.3) proves (3.7).

Behavioral randomizations of distinct players are independent.  The source
opponent survival for `i` factors into the owner survival `p(r)` and the
pair-deleted survival in (3.7).  Multiplying (3.4) and (3.7) proves (3.8).

Equation (3.5) and the checked exact first-disagreement decoder give the paid
row.  Its checked division-free estimate

\[
 \eta/4\le2M\,\text{liveMass}
\]

gives the last lower bound. `QED`

### Fin4 total-gap constant

For Fin4, suppose the total owner-purification leakage obeys

\[
 \sum_{k\ne o}J_k\ge\kappa>0.                      \tag{3.13}
\]

After selecting one of the three outsiders and passing to a subsequence,
Theorem 3.1 applies with `eta=kappa/3`.  Thus one may take

\[
 \begin{aligned}
 \text{paid gain}&\ge\kappa/12,\\
 \text{source owner survival}&\ge\kappa/(48M),\\
 \text{source pair-deleted survival}&\ge\kappa/(24M),\\
 \text{source full opponent survival}&\ge
       \kappa^2/(1152M^2).
 \end{aligned}                                      \tag{3.14}
\]

No mass-good or minimum-fibre assertion is made for the receiving pure-clock
component.

### Corollary 3.2 (zero-owner paid-port preservation)

Assume in addition that

\[
 d_o(\sigma)=0.                                     \tag{3.15}
\]

The owner identity from the pure-time Jensen ledger is

\[
 \mathbb E_{t\sim\pi}d_o(\sigma[t])=d_o(\sigma)=0.  \tag{3.16}
\]

Every summand is nonnegative.  Hence every positive-support component,
including the selected `sigma[a]` and `sigma[b]`, satisfies

\[
 d_o(\sigma[a])=d_o(\sigma[b])=0.                  \tag{3.17}
\]

Use the paid row of Theorem 3.1 to form the
`QuittingPaidCapLiftedSource` whose literal `profile` is `sigma[a]`.  Do not
install `q_a` as the prescribed observer strategy: (3.6) concerns that
response endpoint, but it need not preserve the owner's zero.  At every
finite cap-prefix depth `h`, exact root Nash gives the coordinate identity

\[
 d_o(P_{h+1})
 =\operatorname{ContinueMass}(x_h)d_o(P_h).         \tag{3.18}
\]

Starting from (3.17), induction makes every term in (3.18) zero.  The
summable semantic port is the limit of these literal prefix semantic pairs,
so continuity of the debt coordinate gives

\[
 d_o(\text{port.limit})=0.                          \tag{3.19}
\]

Therefore each charged, quantitative-descent, or inert output of the exact
trichotomy is carried by a semantic port retaining the old owner-zero face.
This does not preserve other old zero coordinates, and it does not say that
the high outsider-response endpoint in (3.6) has owner debt zero.

### Corollary 3.3 (vanishing-owner repair for actual reset approximants)

Let `sigma_n` be actual profiles with fixed owner `o` and outsider `i`, and
assume

\[
 J_{n,i}\ge\eta>0,\qquad
 \delta_n:=d_o(\sigma_n)\longrightarrow0.           \tag{3.20}
\]

Choose `epsilon_n->0` with `0<epsilon_n<=eta/4`.  Define

\[
 L_n=\begin{cases}
 \sqrt{\delta_n},&\delta_n>0,\\
 0,&\delta_n=0.
 \end{cases}                                        \tag{3.21}
\]

After discarding finitely many ranks, Theorem 3.1 can be realized by
supported pairs `a_n,b_n` which retain all of (3.3)--(3.8) and also satisfy

\[
 d_o(\sigma_n[a_n])\le L_n,
 \qquad d_o(\sigma_n[b_n])\le L_n.                 \tag{3.22}
\]

In particular both debts tend to zero.  If the paid-cap source is based at
the unmodified receiving component `sigma_n[a_n]`, then every finite prefix
and the semantic port limit have owner debt at most `L_n`.

#### Proof

For one rank write `delta=d_o(sigma)`.  The owner Jensen identity gives

\[
 \mathbb E_Td_o(\sigma[T])=\delta.                 \tag{3.23}
\]

For any `L>0`, Markov's inequality and a union bound give

\[
 \Pr(d_o(\sigma[T])>L\text{ or }d_o(\sigma[S])>L)
 \le2\delta/L.                                     \tag{3.24}
\]

Suppose there were no pair simultaneously satisfying (3.3), (3.4), and both
owner-debt bounds by `L`.  The tail-bad contribution used in Theorem 3.1 is
at most

\[
 4M\,(2\eta/(16M))=\eta/2,
\]

while (3.24) contributes at most `8M delta/L`.  On the remaining event the
rectangle is below `eta/2`.  Hence

\[
 \mathbb E R\le\eta+8M\delta/L.                   \tag{3.25}
\]

This contradicts `E R>=3eta/2` whenever

\[
 \delta/L<\eta/(16M).                              \tag{3.26}
\]

If `delta_n>0`, the choice (3.21) makes the left side of (3.26)
`sqrt(delta_n)->0`; if `delta_n=0`, Corollary 3.2 gives the result exactly.
Thus the same pair selection eventually retains both owner-debt bounds
without weakening any constant in Theorem 3.1.  Coordinatewise exact
cap-Nash scaling multiplies owner debt by a number in `[0,1]` at every
prefix, so it remains at most `L_n`.  Passing to the semantic-port limit
preserves the same closed inequality. `QED`

The reset-rigid chamber's actual realizing sequence falls under this
corollary, not generally under the exact-zero Corollary 3.2.  The output is
asymptotically on the old owner-zero face; it need not lie exactly on that
face at any finite rank.

## 4. Finite versus escaping first disagreement

Apply Theorem 3.1 along a sequence with fixed `eta,M`.  At every rank, combine
the actual paid component and row with the supplied positive global minimum
to form a `QuittingPaidCapLiftedSource`.  Its summable-port constructor and
`exactTrichotomy` return charged near-return, quantitative debt descent, or
literal inert stall.  Neither the source structure nor either constructor
requires the row's first-disagreement date to be uniformly bounded.  Under
rankwise exact owner zero, Corollary 3.2 makes all these ports exactly
owner-zero.  For the actual reset-rigid realizing sequence, Corollary 3.3
makes their owner debts tend to zero instead.

Independently of that rankwise trichotomy, after a subsequence exactly one of
the following chronological alternatives holds.

1. **Finite switch.** `r_n=r` is fixed.  There is a fixed-gain paid
   first-disagreement row at the same finite depth of an actual supported
   pure-clock component, a response rectangle of size at least `eta/2`, and
   the source survival floors (3.4), (3.7), and (3.8).

2. **Escaping switch (Fin4).** `r_n -> infinity`.  Compactify the complete
   stopping laws of the three opponents of `i` on `Nat union {Never}`.  Let
   `barRoots` be any behavioral root sequence realizing the resulting four
   limiting marginal stopping laws, and write `barRoots_o` for its owner
   hazard.  For every fixed `N`, eventually `r_n>N`, and (3.8) gives

   \[
   \Pr(\text{all three opponents stop after }N)
   \ge\eta^2/(128M^2).
   \]

   Continuity from above in the limiting product law gives

   \[
   \Pr(\text{all three opponents choose Never})
   \ge\eta^2/(128M^2).                              \tag{4.1}
   \]

   In particular, at the compact stopping-law limit,

   \[
   \operatorname{NeverMass}(\texttt{barRoots\_o})\,
   \operatorname{PairDeletedSurvivalLimit}
       (\texttt{barRoots},o,i,0)
   \ge\eta^2/(128M^2).                              \tag{4.2}
   \]

   Thus the escaping Jensen switch reaches the exact
   essential-Never-times-pair-deleted-survival boundary used by the
   finite-splice modulus, but only at the compact law limit.  The receiving
   pure owner clocks also satisfy `a_n>=r_n`, so their selected laws converge
   to `Never`; this extra component fact is not needed for (4.1), which is a
   statement about the original source laws.  The same ranks still carry the
   charged/descent/inert trichotomy from the paragraph preceding the split;
   the compact passport is an additional escaping-arm output, not a
   replacement for the paid-port consumer.

The limit in item 2 need not preserve terminal payoffs, unrestricted caps,
the semantic minimum, or the source's retained atom.  Escape of finite stop
times to `Never` is precisely the discontinuity which makes whole-shift
phantoms possible.

## 5. What this does and does not consume

Combined with Proposition 3.1 of the preceding note, the reset-rigid
pure-time purification now has the following honest exhaustive split:

```text
sum of Jensen gaps -> 0
  -> atom-retaining, zero-preserving near-minimum pure completion;

liminf sum of Jensen gaps > 0
  -> source-visible response rectangle and fixed paid row
     -> rankwise paid-cap trichotomy
        (exactly on the old owner-zero face if d_o=0 rankwise;
         asymptotically on it for the actual reset realizing sequence)
        plus (after a date split)
          fixed first-disagreement depth
          or escaping essential-Never x pair-deleted bubble in a law limit.
```

The second line is stronger than the previously known arbitrary pairwise
switch: it retains a quantitative tail of the original owner law and hence a
full source opponent-survival floor.  It is also a direct full-amplitude
application of `CODEX_STRENGTHEN`'s trace-friction theorem rather than a new
small-reset-square estimate.

It still does not eliminate the reset-rigid chamber.  In either date arm the
rankwise trichotomy can end in the already maintained inert paid port.  The
escaping arm's additional passport supplies no positive per-rank terminal
finite-splice boundary, and its compact law limit need not lie on the minimum
semantic fibre.

## 6. Exact same-table regression for the finite-splice handoff

The distinction in the last paragraph is real.  Use four players
`o,i,a,b`.  Give only player `i` a nonzero reward:

\[
 r_i(S)=\begin{cases}
 1,&\{o,i\}\subseteq S,\\
 0,&\text{otherwise},
 \end{cases}                                        \tag{6.1}
\]

and give every other player reward zero at every terminal coalition.

For each `n`, let

- `o` stop at `n` or `n+1`, each with probability `1/2`;
- `i` play `Never`; and
- `a,b` stop surely at `n+2`.

The actual outcome is always the singleton `{o}`, so every prescribed payoff
is zero.  Player `i` can match either owner date and obtain `1/2`, and no
behavioral response can obtain more.  Therefore

\[
 B_i(\sigma_n)=1/2,\qquad D(\sigma_n)=1/2.          \tag{6.2}
\]

At either deterministic owner component, `i` can match the known date and
obtain one.  Hence

\[
 J_i=\tfrac12(1+1)-\tfrac12=\tfrac12.              \tag{6.3}
\]

The two component-optimal responses are times `n` and `n+1`.  Their rectangle
has value two and first disagreement `r_n=n`.  At that date the original
owner survival, pair-deleted survival of `a,b`, and full opponent survival
are all one.

Nevertheless, at every finite rank and for every possible mover `h`,

\[
 \operatorname{NeverMass}(h)\,
 \operatorname{MaxPairDeletedSurvivalLimit}(\sigma_n,h)=0.   \tag{6.4}
\]

For `h!=i`, its Never mass is zero.  For `h=i`, the Never mass is one, but
after deleting `i` and any one observer, at least one of the remaining
finite-clock players survives only finitely, so the maximum terminal
pair-deleted survival is zero.  The same conclusion holds at every selected
deterministic response endpoint.

After compactification as `n->infinity`, all four marginal stopping laws
converge to `Never`, and the product in (6.4) jumps from zero to one.  Thus a
moving-date bubble cannot be inserted into
`exists_finiteSpliceCutoffs_tendsto_zero_of_capTight` as a positive per-rank
boundary product.  The regression has global minimum debt zero (the
all-Never profile), so it is not a counterexample to the positive-minimum
Fin4 source.  It is an exact counterexample to the purely law-theoretic
handoff from an escaping Jensen switch to a per-rank finite-splice
obstruction.

## 7. Proved and unproved

### Proved here

- the tail-aware response-pair selection (3.3)--(3.5);
- a source-attached pair-deleted floor and full observer-opponent survival
  floor from every fixed positive Jensen gap;
- preservation of the selected owner's zero-debt coordinate through the
  entire rankwise paid-cap port and its semantic limit under exact rankwise
  zero, and the vanishing-owner repair for actual reset approximants;
- the fixed/escaping first-disagreement dichotomy;
- an essential-Never times pair-deleted-survival lower bound in the escaping
  compact law limit; and
- an exact Fin4 same-table regression showing that this limiting obstruction
  need not be positive at any finite rank.

### Not proved

- that the rankwise paid-cap trichotomy avoids its inert arm;
- that the escaping compact law limit retains the positive semantic minimum,
  the reset law, or the marked atom;
- that the per-rank finite-splice boundary product is nonzero; or
- a terminal or uniform-equilibrium consumer for the escaping bubble.

## 8. Declarations and records inspected

- `quittingTerminalPayoff_eq_expect_behaviorStoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`;
- `quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveSlopeRectangle.lean`;
- `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` and
  `QuittingPaidFirstDisagreementRow.gain_le_liveMass` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`;
- `quittingPureTimeFirstDisagreementValue_sub_eq_opponentSurvival_mul` in
  `UniformEquilibrium/Quitting/Paths/SurvivalWeightedSuffixRegret.lean`;
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`;
- `QuittingPaidCapLiftedSource.debt_antitone` and
  `SummableSemanticPort.semantic_tendsto` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`;
- `quittingFiniteSpliceError`,
  `tendsto_quittingFiniteSpliceError_terminal`, and
  `exists_finiteSpliceCutoffs_tendsto_zero_of_capTight` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawFiniteSplice.lean`;
- `quittingPairDeletedSurvivalLimit_eq_prod_neverMass` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawFiniteCapClock.lean`;
- `QuittingPaidCapLiftedSource.exactTrichotomy` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`;
- Theorem 4.1 and Corollary 4.2 of
  `CODEX_STRENGTHEN__CAP_SWITCHING_DELETED_BUBBLE_AND_REPLAY_CONTRACT.md`;
- `CODEX_JOULE__JENSEN_ACTIVE_PASSPORT_DICHOTOMY.md`; and
- `CODEX_EULER__POSITIVE_MINIMUM_FINITE_SPLICE_INERT_BOUNDARY.md` and its
  independent review.

## 9. Export verdict and concrete next question

**Not export-worthy.**  The repaired theorem is a useful internal
source-selection lemma, but it does not yet give a new consumed Fin4 branch:

- every paid row still reaches the existing exact trichotomy, whose inert arm
  remains open;
- neither the fixed-date rectangle nor its port returns the reset law, marked
  atom, or minimum-fibre provenance;
- the escaping cemetery product appears only after compactifying the laws and
  need not be positive in any per-rank finite-splice modulus; and
- the actual reset adapter yields asymptotic owner-zero preservation, not an
  exact rankwise zero face.

The quantitative survival floors need a named downstream consumer before the
result changes the maintained frontier.

Can strict all-Continue uniqueness and the reset-rigid fixed-law incidence
force the compact law limit in the escaping arm to remain on the same
semantic minimum fibre?  Equivalently, can one rule out the Section 6
discontinuity using the retained minimum-law atom or strict toggle, rather
than continuity of stopping laws alone?
