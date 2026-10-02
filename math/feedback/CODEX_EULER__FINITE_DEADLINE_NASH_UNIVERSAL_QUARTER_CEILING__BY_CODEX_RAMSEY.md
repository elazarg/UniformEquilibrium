# Independent review of the finite-deadline universal quarter ceiling

Reviewer: `CODEX_RAMSEY`

Source:
[`CODEX_EULER__FINITE_DEADLINE_NASH_UNIVERSAL_QUARTER_CEILING.md`](../notes/CODEX_EULER__FINITE_DEADLINE_NASH_UNIVERSAL_QUARTER_CEILING.md)

## Verdict

**PASS.**  I independently checked the event decomposition, the unrestricted
behavioral cap reduction, the scalar optimization and constants, the hierarchy
cutoff, and the asymptotic worst-table quantifiers.  The theorem is correct at
its stated scope.

For every exact mixed Nash equilibrium of the timing game with finite actions
`0,...,K-1` and `Never`, every player's unrestricted terminal debt is bounded
by

\[
 R f_K(x),\qquad
 f_K(x)=\frac{x(K+1-(K-1)x)}{K+1+x}
\]

for some `x in (0,1]` whenever that debt is positive.  In particular the
three-date constant is exactly `20-8 sqrt(6) < 5/12`, and the normalized Fin4
midpoint certificate reaches hierarchy level `59`.  The reviewed normalized
Fin4 unique-equilibrium regression gives the matching asymptotic lower bound
`1/4` for the worst hard-tail exact-Nash architecture.

This result is mathematically substantial and suitable for narrow export and
formalization after a separate whole-packet gate.  Its correct architectural
scope is essential: the Nash law is selected afresh after enlarging the timing
menu.  Nothing here preserves a previously selected two-date law, supplies a
soft tail, or produces terminal errors tending to zero.

## 1. Probability semantics and unrestricted cap

Fix player `i`.  Against the opponents' independent planned-time laws, the
events

```text
all opponents choose Never,
opponents' earliest finite time is t,  0 <= t < K
```

are disjoint and exhaustive.  Thus `a + sum_t h_t = 1`, including zero-mass
dates, pure endpoint laws, and a positive or zero Never atom.

Let `V_t` be the payoff of pure time `t<K`, let `V_N` be the Never payoff, and
let `L` be the payoff of any finite time at least `K`.  Finite-game Nash gives
every displayed permitted pure value at most the prescribed payoff.  Since
the prescribed payoff is also their convex combination,

\[
 U_i=\max(V_N,V_0,\ldots,V_{K-1}).
\]

After the opponents' support ends, all later finite pure times have the same
value `L`.  The checked pure-time extremality theorem therefore gives, against
all randomized history-dependent behavioral deviations,

\[
 B_i=\max(U_i,L),\qquad d_i=\max(0,L-U_i).
\]

The standard hazard realization of each finite planned-time law is literal.
Zero conditional denominators occur only after zero-reach histories and do not
alter its stopping law or any payoff.

## 2. Earliest-time comparison

For a fixed `t<K`, compare late Quit with Quit at `t`.

* Opponent exit before `t` gives identical payoffs.
* Opponent exit at `t` gives an opponent-only versus joined-row difference,
  bounded above by `2R`.
* Opponent exit at `u>t` gives an opponent-only reward at most `R` for late
  Quit and the singleton reward `s` for Quit at `t`, hence difference at most
  `R-s`.
* If every opponent chooses Never, both deviations give the singleton reward.

Consequently

\[
 d_i\le \max(0,L-V_t)
 \le 2R h_t+(R-s)\sum_{u>t}h_u.
\]

The use of the positive part is correct even when the raw comparison is
negative.  Late Quit and Never differ only on the all-opponents-Never event,
so `L-V_N=as`.  Thus positive debt forces `s>0` and gives `d_i<=as`.
No late date, tie, or Never boundary is omitted.

## 3. Summation and scalar algebra

With `x=s/R`, `delta=d_i/R`, and `H=sum_t h_t=1-a`, summing the finite-date
comparisons counts `h_u` once for each `t<u`, hence exactly `u` times:

\[
 K\delta
 \le 2H+(1-x)\sum_{u=1}^{K-1}u h_u
 \le (K+1-(K-1)x)H.
\]

Since `delta<=ax`, one has `H<=1-delta/x`.  Writing
`A=K+1-(K-1)x`, which is positive on the stated domain, yields

\[
 \delta\le \frac{Ax}{Kx+A}
 =\frac{x(K+1-(K-1)x)}{K+1+x}.
\]

The boundary `R=0` is separate and trivial; division is used only for
`R>0`, positive debt, and `x>0`.

For `K=3`, differentiation of

\[
 f_3(x)=\frac{x(4-2x)}{4+x}
\]

has numerator `16-16x-2x^2`.  Its unique critical point in `[0,1]` is
`x_*=-4+2 sqrt(6)`, where

\[
 f_3(x_*)=20-8\sqrt6.
\]

The rational estimate is also correct:

\[
 \frac5{12}-f_3(x)
 =\frac{24x^2-43x+20}{12(4+x)}>0,
\]

and the numerator has negative discriminant.  Finally

\[
 f_K(x)
 =\frac{Kx(1-x)+x(1+x)}{K+1+x}
 \le x(1-x)+\frac{x(1+x)}K
 \le \frac14+\frac2K.
\]

All inequality directions are correct.

## 4. Worst-table quantifiers

The note defines `W_K` using the supremum over normalized Fin4 tables and
over **all** exact mixed Nash equilibria of each corresponding `K`-date timing
game.  The universal theorem applies to every such equilibrium, so

\[
 W_K\le c_K\le 1/4+2/K.
\]

Miner's reviewed table has a unique equilibrium at each `K` and debt

\[
 D_K=\frac{2^{K-1}}{2^{K+1}-1}>1/4,
 \qquad D_K\to1/4.
\]

Therefore `W_K>=D_K`, and the squeeze proves `W_K->1/4`.  There is no hidden
interchange of `sup`, `inf`, or horizon-dependent equilibrium choices.  If
one instead studied the best Nash selection at each table, the same example
still supplies the lower bound because its equilibrium is unique, but that is
not needed for the displayed definition.

## 5. Hierarchy cutoff

The actual three-date law is a valid finite-clock center at every hierarchy
support containing those dates.  Its diagonal midpoint has objective zero and
distance at most

\[
 \frac{c_3}{2}=10-4\sqrt6.
\]

For normalized Fin4 the radius is `12/m`.  The exact comparisons

\[
 12/59>10-4\sqrt6,
 \qquad 12/60<10-4\sqrt6
\]

are correctly reduced in the note to integer square comparisons.  Hence the
same center proves `L_M(r)=0` for every `M<=59`; level `60` is only the first
level not covered by this certificate, and the note correctly infers no
positivity there.

## 6. Source, novelty, and disposition

The named checked sources have the stated roles:

* `KernelGame.mixed_nash_exists` supplies finite mixed-Nash existence;
* `sSup_range_quittingTerminalPayoff_update_eq_pureTime` upgrades the
  stopping-time comparison to unrestricted behavioral deviations;
* `QuittingFiniteDeadlineNashProfile` and the late-time identity provide a
  supplied-profile interface but not this producer or scalar bound; and
* the escape-aware hierarchy declarations consume the actual finite-clock
  semantic center.

I found no checked duplicate of the general `f_K` estimate, the exact
three-date constant, or the hard-tail worst-table quarter limit.  A Lean
handoff should keep the quantifiers explicit: first construct/select a Nash
law for the whole `K`-date game, then realize that law behaviorally.  It must
not describe the theorem as appending a date to a fixed earlier equilibrium.

The result is an unrestricted-strategy quantitative producer and an exact
architecture ceiling.  It is not a uniform-payoff theorem and does not change
the current Fin4 rectangle/source-provenance problem.

## 7. Delta review: fixed-prefix finite-tail quarter barrier

**Verdict: REVISE to state the source object literally; mathematical core
PASS.**  Section 8's table, source equilibrium, payoff shift, unrestricted
lower bound, and globally reselected comparison are all correct.  One scope
phrase is not literal: appending a nontrivial tail does **not** preserve the
active players' complete planned-time laws `(1/4,1/4,1/2)`, because their
original `Never` atom is precisely the mass which is reinterpreted as survival
into the appended tail.  Likewise dummies which may activate in the tail do
not retain their complete `Never` laws.  The theorem preserves the first two
hazards, equivalently the two-date **prefix block** and its survival mass.

Replace “preserve these complete first-block laws (and the dummies' initial
Never laws)” by a literal statement such as:

> keep both active players' date-zero and date-one hazards from the unique
> two-date Nash profile, keep both dummies Continue through those two dates,
> and conditionally on joint survival append an arbitrary finite-support
> product behavioral tail.

The title and conclusion should call this a fixed-prefix or fixed two-date
block barrier, not preservation of the complete source law.  With that repair,
the delta is PASS.

For completeness, the calculations are as follows.  With

\[
 r_1(S)=-1\quad\text{iff}\quad\{1,2\}\subseteq S,
 \qquad r_1(S)=1\text{ otherwise},\qquad r_2=-r_1,
\]

the active timing matrix is exactly the reviewed sharp matrix, so its unique
law is `(1/4,1/4,1/2)` and its value is `(1/2,-1/2)`.  Dummy Quit at date zero
or at a positively reached date one has a strictly negative payoff, whereas
Never gives zero, so the source elimination remains valid.

Only joint survival of the active prefix reaches the new tail, with probability
`1/4`.  If its conditional player-1 payoff is `g in [-1,1]`, zero-sum terminal
rows give

\[
 U_1=1/2+g/4,\qquad U_2=-1/2-g/4.
\]

A player-1 pure quit time strictly after the finite tail support always pays
one: if an opponent has quit, player 1 is absent and the terminal coalition
cannot contain both active players; if nobody quits, player 1 exits alone.
Hence

\[
 B_1-U_1\ge 1/2-g/4\ge1/4.
\]

This is an unrestricted lower bound by pure-time extremality.  Under global
reselection, independent uniform clocks on `L` dates give player 1 payoff
`1-2/L`, best-response value one, and debt `2/L`; player 2 and the dummies have
zero debt.  Thus the example is correctly scoped as a fixed-prefix barrier,
not a positive-gap table or a barrier to globally reselected finite clocks.
