# Finite-deadline Nash projective boundary and compatibility criterion

Author: `CODEX_KOLMOGOROV`  
Independent review: [projective-boundary audit](../feedback/CODEX_KOLMOGOROV__FINITE_DEADLINE_PROJECTIVE_BOUNDARY__BY_PROJECTIVE_BOUNDARY_REVIEW.md)

The results below are reviewed ordinary mathematics and do not claim Lean checking. They compare exact finite timing-game Nash equilibria, derive a complete adjacent-deadline quantitative alternative, and prove that an exact compatible family compiles to an all-behavior terminal Nash profile.

## Exact statement and conventions

Let `I` be a nonempty finite player set of cardinality `n`, let `R>0`, and let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow \mathbb R^I
\]

satisfy `|r_i(S)| <= R`.  Put

\[
 A_N=\{0,\ldots,N-1\}\sqcup\{\infty\}.
\]

The deadline-`N` timing game is the finite normal-form game in which the
earliest finite action determines the quitting coalition and the all-`
infinity` outcome pays zero.  A mixed profile always means the independent
product of the players' marginal laws.

For `p in Delta(A_N)^I`, let `L_N p in Delta(A_(N+1))^I` be its literal lift:
old finite dates and `infinity` are unchanged and the new date `N` receives
zero mass.  For `q in Delta(A_(N+1))^I`, let `C_N q in Delta(A_N)^I` censor the
new date by mapping `N` to `infinity`.

For probability laws on one finite action set, `TV` denotes total variation
with the convention

\[
 \operatorname{TV}(\mu,\nu)=\frac12\sum_a|\mu(a)-\nu(a)|.
\]

The question is whether finite timing Nash laws can be selected compatibly
as the deadline grows, and what exact object is forced when they cannot.

## 2. Lipschitz control of a timing gain

Let `P,Q` be two independent mixed profiles on the same finite timing action
set.  Couple every player marginal maximally and independently.  The two pure
action profiles disagree with probability at most

\[
 \sum_j\operatorname{TV}(P_j,Q_j).
\]

Therefore every prescribed payoff coordinate obeys

\[
 |u_i(P)-u_i(Q)|
 \le 2R\sum_j\operatorname{TV}(P_j,Q_j).                 \tag{2.1}
\]

For a fixed pure action `a_i`, the deviating payoff depends only on the
opponent marginals, so

\[
 |u_i(a_i,P_{-i})-u_i(a_i,Q_{-i})|
 \le 2R\sum_{j\ne i}\operatorname{TV}(P_j,Q_j).          \tag{2.2}
\]

Writing

\[
 G_i(a_i;P)=u_i(a_i,P_{-i})-u_i(P),
\]

we obtain

\[
 |G_i(a_i;P)-G_i(a_i;Q)|
 \le 2R\left(
   \operatorname{TV}(P_i,Q_i)
   +2\sum_{j\ne i}\operatorname{TV}(P_j,Q_j)
 \right)
 \le 4R\sum_j\operatorname{TV}(P_j,Q_j).                \tag{2.3}
\]

This is a finite coupling calculation.  No continuity of the infinite timing
game is being asserted.

## 3. Consecutive-Nash projective estimate

Let `p` be any Nash equilibrium of the deadline-`N` timing game and let `q`
be any Nash equilibrium of the deadline-`N+1` timing game.  Write `sigma_p`
for the literal behavioral realization of `p` with all-Continue tail after
date `N`.

All pure dates below `N` and `Never` have nonpositive gain at `sigma_p`.
Every pure date at least `N` has the same payoff as date `N`.  Pure-time
extremality against arbitrary behavioral deviations therefore gives the exact
coordinate debt formula

\[
 d_i(\sigma_p)=\bigl[G_i(N;L_Np)\bigr]_+.                \tag{3.1}
\]

The action `N` belongs to the deadline-`N+1` game, so Nash optimality of `q`
gives

\[
 G_i(N;q)\le0.                                           \tag{3.2}
\]

Combining (2.3)--(3.2) yields, for every player,

\[
 \boxed{
 d_i(\sigma_p)
 \le 4R\sum_j\operatorname{TV}(L_Np_j,q_j).}
                                                               \tag{3.3}
\]

This holds for **every** pair of equilibria at consecutive deadlines; no
equilibrium selection or uniqueness is assumed.

Consequently, if there are deadlines `N_k -> infinity` and consecutive Nash
pairs `(p^k,q^k)` for which

\[
 \sum_j\operatorname{TV}(L_{N_k}p^k_j,q^k_j)\longrightarrow0, \tag{3.4}
\]

then the actual profiles `sigma_(p^k)` have every unrestricted behavioral
terminal debt tending to zero.  The checked terminal-payoff compact selection
then gives a uniform-equilibrium payoff.  Thus asymptotic adjacent
compatibility is already a complete positive criterion; no inverse-limit
realization is needed for this conclusion.

Conversely, suppose there is a global terminal exploitability gap `gamma>0`.
Applying it to `sigma_p` and using (3.3) gives the uniform finite separation

\[
 \boxed{
 \sum_j\operatorname{TV}(L_Np_j,q_j)
 \ge \frac{\gamma}{4R}}
                                                               \tag{3.5}
\]

for every `N` and every `p in NE_N`, `q in NE_(N+1)`.  This is a finite
boundary certificate, not merely the assertion that the profitable time for
one profile lies just beyond its horizon.

### 3.1 A finite semialgebraic upper hierarchy

Define

\[
 \Delta_N(r):=min_{p\in NE_N,\ q\in NE_{N+1}}
   \sum_j\operatorname{TV}(L_Np_j,q_j).                 \tag{3.6}
\]

The minimum exists because both finite-game Nash sets are nonempty compact
semialgebraic sets.  If `eta(r)` is the infimum over all behavioral profiles
of their maximum coordinate terminal debt, (3.3) gives

\[
 \boxed{\eta(r)\le4R\Delta_N(r)}                        \tag{3.7}
\]

for every `N`.  Hence `inf_N Delta_N(r)=0` is a finite exact semialgebraic
sufficient criterion for a uniform-equilibrium payoff, and a supplied pair
with small distance produces the required actual low-debt profile.  Under a
positive terminal gap, (3.5) is precisely the opposite uniform lower bound on
all these finite queries.

This hierarchy is not complete for zero gap: the hard-deadline regression in
Section 6 has a fixed boundary clock and keeps the adjacent distance away from
zero even though its table has a uniform-equilibrium payoff.  Thus (3.7) is a
new finite positive certificate, not a decision procedure.

## 4. Finite-versus-Never decomposition

For a deadline-`N+1` law `q_j`, put

\[
 b_j=q_j(N),\qquad
 e_j=\operatorname{TV}(p_j,C_Nq_j).                     \tag{4.1}
\]

Here `b_j` is new finite participation at the exposed boundary date, while
`e_j` is failure of the old law to agree after that participation is censored
back into `Never`.  Moving the mass `b_j` from `N` to `infinity` has total
variation exactly `b_j`; hence

\[
 \operatorname{TV}(L_Np_j,q_j)\le e_j+b_j.              \tag{4.2}
\]

Under a global gap, (3.5) and (4.2) give the exact exhaustive alternative

\[
 \boxed{
 \sum_j b_j\ge\frac{\gamma}{8R}
 \quad\text{or}\quad
 \sum_j e_j\ge\frac{\gamma}{8R}.}                       \tag{4.3}
\]

Thus every attempted adjacent projective selection pays either a macroscopic
new-deadline participation defect or a macroscopic reshuffling defect on the
already exposed clock.

### 4.1 The boundary-participation arm gives a response collision

Assume `n>=2` and the first arm of (4.3).  Select `j` with

\[
 b_j\ge\frac{\gamma}{8Rn}.                              \tag{4.4}
\]

Apply the global gap to the behavioral realization of `q`.  The checked
finite-deadline escape bound selects a player `h` with positive singleton
reward and with every opponent's declared `Never` mass at least

\[
 a:=\frac{\gamma}{R}.                                   \tag{4.5}
\]

(More sharply one may use `gamma/r_h({h})`.)  If `j != h`, let `i=h`; if
`j=h`, choose any `i != h`.  Replace player `i` by the deterministic deadline
`N`.  The event

\[
 T_j=N,qquad T_k=\infty\quad(k\notin\{i,j\})
\]

then produces the literal pair coalition `{i,j}` at date `N`.  Every displayed
`Never` factor is covered by (4.5), so the response profile has the
source-matched atom

\[
 \boxed{
 \Pr(\{i,j\}\text{ at date }N)
 \ge
 \frac{\gamma}{8Rn}\left(\frac{\gamma}{R}\right)^{n-2}.}
                                                               \tag{4.6}
\]

For `Fin 4`, the floor is `gamma^3/(32 R^3)`.

This is a counterfactual response atom, not necessarily an atom of prescribed
play and not necessarily a profitable response at the deadline-`N+1`
equilibrium.  That distinction is essential.

### 4.2 Every adjacent boundary gives a paid edge or paid response square

There is a stronger strategic localization which does not need to split
between `b` and `e`.  Assume `n>=2` and let `i` be a gap witness for `p`, so

\[
 G_i(N;L_Np)\ge\gamma.                                  \tag{4.7}
\]

Here and below, `Q_N` denotes the deterministic timing law, equivalently the
pure-time behavioral strategy, which Quits at date `N`.  Every finite-clock
profile in this subsection has the common hard all-Continue suffix **strictly
after** date `N`; a response corner using `Q_N` itself absorbs at date `N`.

Join `L_Np` directly to `q` by replacing the `n-1` opponent marginals, in any
fixed order, and replacing player `i`'s own marginal last.  Write the
resulting chain as `H_0,...,H_n`.  Its first response gain is at least
`gamma`, while Nash optimality of `q` gives `G_i(N;H_n)<=0`.  There are two
cases.

\[
 G_i(N;H_0)\ge\gamma,qquad G_i(N;H_n)\le0.              \tag{4.8}
\]

If every opponent-hybrid still satisfies

\[
 G_i(N;H_k)>\frac{3\gamma}{4}qquad(0\le k<n),           \tag{4.9}
\]

then the final own-law replacement has fixed opponents, so its response
payoff is unchanged.  Since `G_i(N;H_n)<=0`,

\[
 \boxed{U_i(H_n)-U_i(H_{n-1})>\frac{3\gamma}{4}.}       \tag{4.10}
\]

This is an actual paid unilateral whole-stopping-law edge, and its source
still carries a pure-deadline gain above `3 gamma/4`.

Otherwise let `k<n` be the first opponent-hybrid with
`G_i(N;H_k)<=3 gamma/4`.  The total signed drop before that crossing is at
least `gamma/4`.  Among at most `n-1` opponent replacements there are
consecutive actual product profiles `A,B`, differing only in one player
`j != i`, such that

\[
 G_i(N;A)>\frac{3\gamma}{4},
 \qquad
 G_i(N;A)-G_i(N;B)
 \ge\frac{\gamma}{4(n-1)}.                              \tag{4.11}
\]

The second inequality is the exact common-response square

\[
 \begin{aligned}
 &[U_i(A[i\leftarrow Q_N])-U_i(A)]\\
 &\quad-[U_i(B[i\leftarrow Q_N])-U_i(B)]
 \ge\frac{\gamma}{4(n-1)}.                              \tag{4.12}
 \end{aligned}
\]

Thus the rectangle comes with a **paid source**: at `A`, the same displayed
pure response already gains more than `3 gamma/4`.  All four profiles are
literal finite-clock behavioral profiles with the same hard all-Continue
suffix.  Adjacent-horizon incompatibility therefore localizes to either a paid
own-law edge or a paid source-matched response rectangle, not merely a
total-variation diagnostic.

Equations (4.6), (4.10), and (4.12) still lack positive-minimum source
provenance.  They should not be identified with the current minimum-fibre
collision or rectangle packets without a separate reprojection theorem.

### 4.3 The exact retained-tail seam

The obstruction to simply grafting a minimum source behind the preceding
profiles is one scalar, but it is not automatically small.  If `P` is a hard
finite-clock product law, let

\[
 M(P)=\prod_j P_j(\infty)
\]

be its joint pass mass.  Replacing the zero hard tail by an actual retained
tail of payoff `u` changes the prescribed payoff exactly by

\[
 U_i^u(P)=U_i^0(P)+M(P)u_i.                             \tag{4.13}
\]

The pure deadline just before that tail absorbs whenever it is relevant, so
its payoff is tail-independent.  Consequently

\[
 G_i^u(N;P)=G_i^0(N;P)-M(P)u_i.                         \tag{4.14}
\]

For a response square between `A` and `B`, the cross-difference therefore
acquires the exact seam

\[
 -(M(A)-M(B))u_i.                                       \tag{4.15}
\]

Thus the paid rectangle survives reprojection to a minimum tail if, for
example, `|M(A)-M(B)| |u_i|` is smaller than its fixed cross floor.  The
adjacent timing argument does not supply that estimate.  This identifies a
concrete next adapter: retain or equalize joint finite-versus-Never
participation along the selected hybrid edge.  Merely substituting a
semantically desirable tail is invalid.

### 4.4 Regression: zero-pass equalization need not retain charge or pay for its correction

The most direct repair of (4.15) is to change one common coordinate in both
columns so that its `Never` mass is zero.  Then both joint pass masses vanish.
A local theorem saying that this either retains a fixed part of the response
square or makes the correcting unilateral edge profitable is false, even with
four players and literal one-date profiles.

Let the players be `1,2,3,4`, with observer `1`, mover `2`, and spares `3,4`.
Define

\[
 r_1(S)=\begin{cases}1,&S=\{1\},\\0,&S\ne\{1\},\end{cases}
 \qquad r_k(S)=0\quad(k\ne1).                           \tag{4.16}
\]

Let the retained tail `tau` make player `1` Quit surely and every other
player Continue, so `U_1(tau)=1`.  At the boundary date let `A` make every
player Continue into `tau`, and let `B` differ from `A` only by making player
`2` Quit surely.  With the hard zero tail, the observer's `Q_N` gain is `1`
at `A` and `0` at `B`: the hard response-square charge is exactly `1`.

After grafting `tau`, however,

\[
 U_1(A)=U_1(A[1\leftarrow Q_N])=1,
 \qquad
 U_1(B)=U_1(B[1\leftarrow Q_N])=0.                    \tag{4.17}
\]

Thus both retained-tail response gains are zero.  Here `M(A)=1`, `M(B)=0`,
and `u_1=1`, so the seam in (4.15) is `-1` and cancels the hard charge
exactly.

There is no payment hidden in the natural common-coordinate corrections.
Forcing observer `1` to `Q_N` in both columns makes both response gains
identically zero, while the actual observer-own payoff change is zero in each
column by (4.17).  Forcing either spare `3` or `4` to `Q_N` also makes both
joint pass masses zero and both observer response gains zero.  The correcting
spare's own payoff change is zero because every one of its rewards is zero.
The observer payoff lost when a spare changes is not an executable unilateral
gain of that spare and therefore cannot be counted as a paid correction edge.

This is a regression for the proposed local `2 x 2` equalization principle,
not for a positive-minimum source theorem.  The table has `D_*=0` because the
retained-tail profile itself is exact.  Positive-minimum
provenance would have to supply an additional sign or minimality inequality
which rules out this exact cancellation; joint-pass equalization and local
cube bookkeeping alone do not.

## 5. Exact projective systems

Suppose one can choose `p^N in NE_N` for every positive `N` so that

\[
 C_Np^{N+1}=p^N.                                       \tag{5.1}
\]

Then the marginals form the truncations of unique probability laws `mu_i` on
`Nat union {infinity}`.  Explicitly, the mass exposed at date `N` is
`p_i^{N+1}(N)`, and consistency makes the old finite atoms permanent while
the `Never` mass is their remaining tail.  In particular

\[
 p_i^{N+1}(N)=\mu_i(N)\longrightarrow0.                 \tag{5.2}
\]

Equations (3.3), (5.1), and (5.2) already give terminal approximate Nash
profiles.  More strongly, the independent laws `mu_i` realize an exact
behavioral terminal Nash profile.  Indeed, prescribed terminal payoffs of the
truncations converge to the payoff of `mu`: the only missing event is finite
absorption after the cutoff, whose probability tends to zero.  Every fixed
finite pure-time inequality passes from `p^N` once `N` is beyond that time;
the `Never` inequality passes by the same bounded-convergence argument.
Pure-time extremality then covers every behavioral deviation.

Therefore

\[
 \boxed{
 \text{an exact projectively compatible family of timing Nash laws}
 \Longrightarrow
 \text{an exact behavioral terminal Nash profile}.}    \tag{5.3}
\]

This also explains why separate finite equilibria cannot simply be treated as
an inverse system.  Exact compatibility is already strong enough to solve the
terminal problem.

By compactness, absence of such a family has a finite witness: there is a
finite depth at which the compact set of exactly compatible Nash chains is
empty.  Equivalently, at that depth the continuous maximum compatibility
error has a positive minimum.  Here the depth-`D` compatibility error means
the minimum, over the compact product `NE_1 x ... x NE_D`, of the maximum of
**all** adjacent censoring errors in that chain.  It is not the single-edge
quantity `Delta_N` from (3.6).  This abstract finite witness is weaker than
(3.5), which gives an explicit table-level lower bound at every adjacent
depth under a global gap.

## 6. Sharp regression: boundary participation can be nonterminal

The checked hard-deadline table in
`FinFourHardDeadlineTimingNashUniqueness.lean` has one unique Nash law at every
deadline and unrestricted debt tending to `1/4`, although the same quitting
game has a uniform-equilibrium payoff.  The associated opponent Never mass
tends to `1/2`; the debt is half of that mass.  In the two active coordinates
used by the construction, the late opponent's newly exposed last-date mass is

\[
 b_N=\frac{2^N}{2^{N+2}-1}\longrightarrow\frac14.        \tag{6.1}
\]

The prescribed probability of actually reaching that last date tends to
zero because the other active clock is uniform over the earlier dates.  But
when the debtor is replaced by the newly available pure deadline, (6.1)
becomes a simultaneous response collision of asymptotic mass `1/4`; that is
exactly what changes the late deviation payoff.

Thus a boundary participation atom is naturally a **response** atom, not a
prescribed terminal atom.  The table has global minimum debt zero, so it also
shows that (4.6) or (4.12) without positive-minimum provenance is not by itself
a Fin4 consumer.

## 7. Retained-tail regression: tail charge does not force a second timing Nash

The following exact two-player table addresses the retained-tail question.
Coordinates are ordered `(1,2)`:

\[
 r(\{1\})=(-1,0),\qquad
 r(\{2\})=(2,-1),\qquad
 r(\{1,2\})=(1,1).                                    \tag{7.1}
\]

Let the actual retained tail `tau` make both players Quit surely at its first
date.  Then

\[
 U(\tau)=(1,1),\qquad
 U_i(\tau)-r_i(\{i\})=2\quad(i=1,2),                   \tag{7.2}
\]

while player 1 has tail debt `1`: by Continuing at the tail row it receives
`r_1({2})=2` instead of `1`.

Nevertheless, for every finite retained-tail timing horizon, the unique mixed
Nash equilibrium is pure all-`infinity`, i.e. pass through the whole word to
`tau`.

To prove uniqueness, suppose a Nash profile gives positive mass to some
finite time and choose the earliest finite time `t` used by either player.

* If only player 1 uses `t`, then on that event it Quits alone for `-1`, while
  passing either receives `2` from player 2's later singleton exit or `1` from
  the retained tail.
* If only player 2 uses `t`, the same comparison is `-1` versus `0` or `1`.
* If both use `t`, player 1 gets `1` by matching but `2` by passing and letting
  player 2 Quit alone.

In every case the purported earliest finite action is not a best response, a
contradiction.  Thus both players pass surely.  Against a passing opponent,
passing pays `1` and every finite action pays the singleton reward `-1`, so
all-`infinity` is indeed strict and unique.

This tail therefore has a literal source-attached paid response and the
uniform separation required by the nonidentity absorption-floor lemma, yet it
does not produce a nonidentity timing equilibrium at any horizon.  The example
may be preceded by arbitrarily many literal all-Continue roots, so the same
paid suffix response persists at arbitrarily deep retained-tail entrances.
It is nevertheless suffix charge, not charge of a nonidentity timing block.
The example
has global minimum debt zero (all-Never is exact), so it does not refute a
producer using full positive-minimum provenance.  It does prove that tail
charge, singleton separation, and finite timing Nash existence alone cannot
force the second equilibrium needed by the two-sided-charge route.

The absorption-floor comparison in this paragraph is the unreviewed ordinary-
mathematics result recorded in
`notes/CODEX_ROOT__NONIDENTITY_RETAINED_TAIL_TIMING_NASH_TWO_SIDED_CHARGE.md`.
It is not a theorem of the checked retained-tail modules cited below.  Those
modules provide the checked debt transport and, under their stated global-gap
and punishment hypotheses, the checked return floor.

## 8. Source audit and exact scope

The following checked declarations were inspected directly:

* `exists_finiteDeadlineTimingNash_terminalDebt_le` in
  `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingNashDebt.lean`;
* `timingMixedPayoff_bellman`,
  `timingLawTail_isNash_of_isNash_of_positiveContinue`, and
  `finiteDeadlineTimingProfile_spine_one_eq_tail` in
  `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingRecursion.lean`;
* `QuittingFiniteDeadlineNashProfile.bestResponseValue_le_max_late` in
  `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineNashDebtBounds.lean`;
* `IsQuittingRetainedTailFiniteTimingNash.debt_le_deletedReturn_mul_tailDebt`
  in `UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingNash.lean`;
* `terminalGap_retainedTailFiniteTimingNash_jointReturn_ge` in
  `UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingReturnFloor.lean`;
* the unique hard-deadline law and debt theorems in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashUniqueness.lean`;
* `hardDeadlineDebt_eq_normalizedGeometric`,
  `tendsto_hardDeadlineDebt_succ_quarter`, and
  `comparisonTarget_isUniformEquilibriumPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashBarrier.lean`.

The exact adjusted late-debt identity and the coherent backward recursion were
also checked against Sections 3--12 of
`notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`; the short horizon-escape
form was checked against
`notes/CODEX_FERMAT__FINITE_DEADLINE_NASH_HORIZON_ESCAPE.md`.  The present note
does not re-claim those results.

Logical level:

* (3.3)--(4.12) are an unconditional finite-game comparison and a conditional
  global-gap boundary producer;
* Section 4.4 is an exact local regression to a joint-pass cube repair, on a
  table with global minimum debt zero;
* (5.3) is a supplied compatible-family completeness theorem;
* Section 7 is an exact local impossibility result;
* none of them produces positive-minimum source provenance, consumes the
  current Fin4 inert SCC, or constructs a positive-gap reward table.

## 9. Next question

Can the paid edge or common-response square in (4.10)--(4.12) be reprojected
to one minimum-fibre source without losing the consecutive-deadline boundary
separation?  A positive answer would turn the finite-horizon incompatibility
certificate into the source-coherent response chart sought by the current
Fin4 atlas.  A negative answer should realize (4.12) at every deadline on a
single positive-minimum-compatible table while proving that every such square
changes its observer or response witness.


## Conjecture-facing change

The usual finite-horizon obstruction says only that a profitable pure time may escape immediately beyond each chosen deadline.  This packet proves a stronger finite obstruction: under a terminal gap, **every** pair of Nash laws at consecutive deadlines is separated by at least `gamma/(4R)` in summed marginal total variation.  That separation localizes unconditionally to a fixed-gain paid unilateral edge or a genuinely paid common-response rectangle, and also splits into exposed boundary participation versus censored-law reshuffling.  Conversely, adjacent compatibility tending to zero already gives actual all-behavior terminal approximate Nash profiles; an exact compatible inverse family gives an exact terminal Nash profile.

The remaining source adapter is explicit: the paid edge/rectangle is built from finite-clock Nash laws with the hard all-Continue suffix, not from the maintained positive-minimum causal source.  A minimum-fibre reprojection retaining the adjacent-deadline separation is still required before this result can consume the Fin4 inert SCC.

## Adapter and consumer

The input is arbitrary exact Nash data `p in NE_N`, `q in NE_(N+1)` from the finite strategic timing games; Nash existence supplies such data for every finite table and deadline.  The output has two complete consumers:

1. if the adjacent distances tend to zero, inequality (3.3) gives literal finite-clock profiles with every unrestricted terminal debt tending to zero, after which the checked terminal-to-uniform compact selection applies;
2. if an exact censor-compatible family is supplied, Section 5 constructs its limiting independent stopping laws and proves an exact terminal Nash profile against every behavioral deviation.

Under a hypothetical positive gap, the alternative output is the finite paid edge/rectangle of Section 4.  Its still-open consumer is a source-faithful minimum-fibre reprojection or another direct chronology compiler.

## Lean handoff

Suggested declarations should separate the finite coupling core from the source adapter:

```text
finiteDeadlineTimingGain_lipschitz_totalVariation

finiteDeadlineTimingNash_debt_le_adjacentDistance

terminalGap_adjacentTimingNash_totalVariation_ge

finiteDeadlineNashAdjacentDistance

terminalExploitabilityInf_le_four_mul_bound_mul_adjacentDistance

consecutiveTimingNash_paidEdge_or_paidResponseSquare

projectivelyCompatibleFiniteTimingNash_exists_terminalNash
```

The semialgebraic hierarchy should quantify over the exact finite Nash sets and use a max/graph presentation compatible with the existing polynomial outer-query infrastructure.  The common response `Q_N` must be the newly exposed boundary date, and all finite profiles use the same hard all-Continue suffix strictly after that date.

## Scope and nonclaims

- No positive-gap table is constructed.
- A positive lower bound on `Delta_N` does not imply a positive terminal gap; the proved inequality is `eta(r) <= 4R Delta_N(r)`.
- Boundary response atoms are counterfactual atoms, not necessarily prescribed terminal atoms.
- The paid finite-clock rectangle has no checked positive-minimum source attachment.
- The retained-tail and joint-pass regressions have global minimum zero and only rule out local conversions.
- No Lean, adapter, or downstream Fin4 consumer seal is claimed by this packet.

## Lean formalization record

Pre-formalization packet SHA-256:
`34ca057e16a1fd047cc89690054adc5ea9e4313d84798427306a35e6af438648`.
The sentence immediately above records the packet's pre-formalization status
and is superseded by this checked record.

The initial Research implementation landed in commit
`333ab076641e9004a124ed68c65ff94ff9c6a333`; production promotion and literal
retained-tail realization landed in
`0156bc55132ffb47ba6145fc87481f73fd8cbbda`; the adjacent-gap source,
collision, hybrid dispatch, and null-direction regression landed in
`b0000fcb5213f6b25538ba3256b8d46985c4e4d2`.

The production owners are
`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineAdjacentTotalVariation.lean`,
`CensoredFiniteClockOperationalEffect.lean`,
`FiniteDeadlineProjectiveCompatibility.lean`,
`ProjectiveTimingInverseLimit.lean`,
`FiniteDeadlineVanishingAdjacentDistance.lean`,
`RetainedTailFiniteTimingRealization.lean`, `AdjacentDeadlineGapSource.lean`,
`FiniteDeadlineBoundaryResponseCollision.lean`,
`FiniteDeadlineTimingHybridDispatch.lean`, and
`FinFourCensoredClockNullDirection.lean`, all under the same Diagnostics
directory.

The principal checked declarations are
`quittingFiniteDeadlineTimingProfile_semanticDebt_le_adjacentTV`,
`quittingFiniteDeadlineAdjacentTV_ge_div_of_semanticDebt_ge`,
`exists_uniformEquilibriumPayoff_of_arbitrarilySmallAdjacentNashTV`,
`QuittingFiniteDeadlineCompatibleNashFamily.exists_uniformEquilibriumPayoff`,
`QuittingFiniteDeadlineCompatibleNashFamily.isZeroAsymptoticNash_limitProfile`,
`QuittingFiniteDeadlineCompatibleNashFamily.isUniformEquilibriumPayoff_limitProfile`,
`quittingGame_isUniformEquilibriumPayoff_of_adjacentTV_tendsto`,
`QuittingAdjacentDeadlineGapSource.censoredError_or_boundaryParticipation`,
`quittingAdjacentDeadline_paidOwnEdge_or_paidResponseSquare`,
`QuittingFiniteDeadlineBoundaryResponseCollision.behavioralStagePairMass_ge_finFour`,
and `FinFourCensoredClockNullDirection.regressionCertificate`.

Evidence seals are `M`, `L`, and `C` for supplied vanishing-adjacent or exact
compatible families.  There is no compatible-family source `A`;
`FiniteCompatibleChainsProduceProjectiveNashFamily` remains only an open
Research proposition.  No positive-gap table or minimum-fibre attachment is
constructed.  Response squares are not asserted profitable, the collision is
counterfactual rather than prescribed play, and the regressions have zero
global minimum debt.
