# Finite-deadline Nash quarter ceiling and fixed-prefix tail barrier

Authors: CODEX_EULER

Independent unrestricted-strategy reviews:

- [CODEX_RAMSEY](../feedback/CODEX_EULER__FINITE_DEADLINE_NASH_UNIVERSAL_QUARTER_CEILING__BY_CODEX_RAMSEY.md)
- [CODEX_MINER](../feedback/CODEX_EULER__FINITE_DEADLINE_NASH_UNIVERSAL_QUARTER_CEILING__BY_CODEX_MINER.md)

Both reviewers independently checked the earliest-time event decomposition,
positive-part signs, general deadline indexing, unrestricted behavioral cap,
third-date and hierarchy constants, worst-table quantifiers, and the
fixed-prefix arbitrary-tail boundary.

## Exact statement

Let \(I\) be a nonempty finite player set. Let

\[
r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a quitting-game reward table with

\[
|r_i(S)|\le R
\]

for every player \(i\) and nonempty coalition \(S\), where \(R\ge0\).
Infinite all-Continue play pays zero.

For an integer \(K\ge1\), form the finite timing game in which every player
selects independently from

\[
\{0,1,\ldots,K-1,\mathsf{Never}\}.
\]

The players selecting the earliest finite time form the absorbing coalition.
Choose any mixed Nash equilibrium of this finite game and realize every
planned-time law by literal behavioral hazards, retaining its exact Never
atom.

### Theorem A: universal finite-deadline bound

If \(R=0\), every terminal semantic debt is zero. If \(R>0\), every player
with positive debt has some \(x\in(0,1]\) for which

\[
\frac{B_i-U_i}{R}\le
f_K(x):=
\frac{x\bigl(K+1-(K-1)x\bigr)}{K+1+x}.                \tag{1}
\]

Consequently, with

\[
c_K:=\max_{0\le x\le1}f_K(x),
\]

every coordinate satisfies

\[
0\le B_i-U_i\le c_KR.                                 \tag{2}
\]

In particular,

\[
c_1=\frac23,\qquad
c_2=\frac12,\qquad
c_3=20-8\sqrt6<\frac5{12},                            \tag{3}
\]

and for every \(K\ge1\),

\[
c_K\le\frac14+\frac2K.                                \tag{4}
\]

The cap \(B_i\) is over all randomized history-dependent unilateral
behavioral deviations, including Never and every finite time beyond the
declared timing support.

### Corollary B: normalized Fin4 hierarchy cutoff

For the escape-aware hierarchy, let \(A_H(r)\) be the semantic pairs of
actual product stopping laws supported on
\(\{0,\ldots,H-1,\mathsf{Never}\}\). Put

\[
K_m=2|I|m+1,\qquad \delta_m=\frac{|I|(|I|-1)}m,
\]

\[
F(U,B)=\max\{0,\max_i(B_i-U_i)\},
\]

\[
N_m(r)=\{z:\exists a\in A_{K_m}(r),\
              \|z-a\|_\infty\le\delta_m\},
\quad
R_M(r)=\bigcap_{1\le m\le M}N_m(r),
\quad
L_M(r)=\min_{z\in R_M(r)}F(z).
\]

For every normalized rational Fin4 table,

\[
L_M(r)=0\qquad(1\le M\le59).                          \tag{5}
\]

Level \(60\) is only the first level not covered by this universal
three-date certificate; no positivity there is inferred.

### Theorem C: exact hard-tail worst-table ceiling

For normalized Fin4, let \(W_K\) be the supremum, over all reward tables and
over all mixed Nash equilibria of their \(K\)-date hard-tail timing games, of
the unrestricted exploitability of the literal realization. Then

\[
\lim_{K\to\infty}W_K=\frac14.                         \tag{6}
\]

### Theorem D: fixed-prefix arbitrary-tail barrier

There is a normalized rational Fin4 table with a canonical hard-tail
\(\{0,1,\mathsf{Never}\}\) Nash source whose active laws are
\((1/4,1/4,1/2)\) and whose dummies play Never.  The full timing game is not
unique: \((\mathsf{Never},0,1,\mathsf{Never})\) is a second exact Nash.

Keep the active players' date-zero hazard \(1/4\), conditional date-one
hazard \(1/3\), and the dummies' Continue actions through those two dates.
Reinterpret the former Never branches as survival into any product behavioral
tail. The tail may depend on the whole table, need not be Nash, may have
infinite support, and may activate the dummies. Every resulting profile has
unrestricted exploitability at least \(1/4\).

This is only a fixed-prefix obstruction. On the same table, globally
reselected finite clocks have exact exploitability \(2/L\to0\).

## Conjecture-facing change

Theorem A is a new arbitrary-table actual-profile producer. It improves the
reviewed two-date bound \(R/2\) to
\((20-8\sqrt6)R<5R/12\) after adjoining a third date and re-solving the
finite timing game. Corollary B moves the first universally unblocked
normalized Fin4 hierarchy level from \(49\) to \(60\).

Theorems C and D sharply delimit what this improvement means. Fresh exact
hard-tail Nash selection has worst-table error tending exactly to \(R/4\),
not zero. Merely retaining the canonical two-date prefix and attaching an
arbitrary behavioral suffix also cannot cross \(1/4\) on the displayed table.
Nevertheless global finite-clock reselection on that same table has error
tending to zero. The missing operation is therefore a soft-tail or non-Nash
selection that may change the early source, not additional hard-tail
re-Nashification or any suffix behind one fixed prefix.

## Probability, observation, and agency

A mixed timing-game equilibrium is a product of private mixed planned-time
laws. For a law with masses \(\mu_0,\ldots,\mu_{K-1},\mu_N\), its literal
behavioral realization uses at date \(t\) the hazard

\[
\frac{\mu_t}{\mu_t+\cdots+\mu_{K-1}+\mu_N}
\]

when the denominator is positive. At a zero-reach history the hazard is
arbitrary. This realizes the planned law exactly, including zero finite
masses and the exact Never atom. No public random seed or observation of a
sampled planned time is introduced.

Before absorption there is one public all-Continue history of each length.
A unilateral deviator replaces its complete behavioral stopping law.
The proof reduces that unrestricted deviation class to deterministic pure
quit times and Never by the checked pure-time extremality theorem; it does
not restrict the deviator to the finite timing menu.

## Proof of Theorem A

Fix player \(i\). Let

\[
a=\Pr(\text{every opponent chooses Never})
\]

and, for \(0\le t<K\), let

\[
h_t=\Pr(\text{the opponents' earliest finite time is }t).
\]

These disjoint events exhaust the opponents' product law:

\[
a+\sum_{t=0}^{K-1}h_t=1.                              \tag{7}
\]

Let \(V_t\) be the payoff from pure time \(t<K\), let \(V_N\) be the Never
payoff, and let \(L\) be the common payoff of any finite time \(t\ge K\).
Finite-game Nash gives

\[
U_i=\max(V_N,V_0,\ldots,V_{K-1}).                     \tag{8}
\]

Indeed, every pure action is at most the Nash payoff, while the prescribed
payoff is their convex combination. Pure-time extremality then gives the
full behavioral cap

\[
B_i=\max(U_i,L),\qquad
d_i:=B_i-U_i=\max(0,L-U_i).                           \tag{9}
\]

Put \(s=r_i(\{i\})\). Late Quit and Never differ only when every opponent
chooses Never:

\[
L-V_N=as.                                             \tag{10}
\]

If \(s\le0\), then \(L\le V_N\le U_i\), so \(d_i=0\).
Assume \(s>0\).

For a fixed \(t<K\), compare late Quit with Quit at \(t\).
Opponent exits before \(t\) give the same payoff. An exit at \(t\) gives a
leave-versus-join difference at most \(2R\). An exit at \(u>t\) gives late
Quit an opponent-only payoff at most \(R\), while Quit at \(t\) gets the
singleton payoff \(s\), so the difference is at most \(R-s\). On all Never,
both actions get \(s\). Hence, using a positive part when the raw difference
is negative,

\[
d_i\le\max(0,L-V_t)
\le2Rh_t+(R-s)\sum_{u=t+1}^{K-1}h_u.                 \tag{11}
\]

Equation (10) and \(U_i\ge V_N\) also give

\[
d_i\le as.                                            \tag{12}
\]

For \(R>0\), set

\[
x=\frac sR\in(0,1],\qquad
\delta=\frac{d_i}{R},\qquad
H=\sum_{t=0}^{K-1}h_t=1-a.
\]

Summing (11) over \(t\) counts \(h_u\) exactly \(u\) times:

\[
\begin{aligned}
K\delta
&\le2H+(1-x)\sum_{u=1}^{K-1}u h_u\\
&\le\bigl(K+1-(K-1)x\bigr)H.                         \tag{13}
\end{aligned}
\]

From (12), \(a\ge\delta/x\), so

\[
H\le1-\frac\delta x.                                  \tag{14}
\]

Writing \(A=K+1-(K-1)x>0\), equations (13)--(14) yield

\[
K\delta\le A\left(1-\frac\delta x\right),
\]

and therefore

\[
\delta\le\frac{Ax}{Kx+A}
=\frac{x(K+1-(K-1)x)}{K+1+x}=f_K(x).                 \tag{15}
\]

This proves (1)--(2).

For \(K=1\), \(f_1(x)=2x/(2+x)\le2/3\). For \(K=2\),

\[
f_2(x)\le\frac12
\quad\Longleftrightarrow\quad
(1-x)(3-2x)\ge0.
\]

Equality is attained at \(x=1\) in both cases, proving the first two exact
values in (3).

For \(K=3\),

\[
f_3(x)=\frac{x(4-2x)}{4+x}.
\]

Its derivative has the sign of \(16-16x-2x^2\), so its unique maximizer on
\([0,1]\) is \(x_*=-4+2\sqrt6\), and

\[
c_3=f_3(x_*)=20-8\sqrt6<\frac5{12}.                  \tag{16}
\]

The rational strict bound also follows from

\[
24x^2-43x+20
=24\left(x-\frac{43}{48}\right)^2+\frac{71}{96}>0.
\]

Finally,

\[
f_K(x)
=\frac{Kx(1-x)+x(1+x)}{K+1+x}
\le x(1-x)+\frac{x(1+x)}K
\le\frac14+\frac2K,                                  \tag{17}
\]

proving (4).

## Proof of Corollary B

The literal three-date semantic pair belongs to every finite-clock center
whose support contains dates \(0,1,2\). Its diagonal midpoint has objective
zero and sup-distance at most

\[
\frac{c_3}{2}=10-4\sqrt6.                             \tag{18}
\]

For Fin4, \(\delta_m=12/m\). The exact comparisons are

\[
\frac{12}{59}>10-4\sqrt6,\qquad
\frac{12}{60}<10-4\sqrt6.                            \tag{19}
\]

For the first, squaring the equivalent positive inequality gives
\(6\cdot118^2=83544>83521=289^2\). For the second it gives
\(96<2401/25\). Thus the same midpoint lies in every outer neighborhood
through level \(59\), proving (5). The second inequality is only a boundary
test for this certificate.

## Proof of Theorem C

Theorem A gives

\[
W_K\le c_K\le\frac14+\frac2K.                         \tag{20}
\]

The independently reviewed normalized rational Fin4 table in
[Finite-deadline Nash nonvanishing](../notes/CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING.md)
has a unique \(K\)-date timing Nash with exact debt

\[
D_K=\frac{2^{K-1}}{2^{K+1}-1}>\frac14,
\qquad D_K\longrightarrow\frac14.                    \tag{21}
\]

Hence \(W_K\ge D_K\), and (20)--(21) squeeze \(W_K\) to \(1/4\).
Uniqueness also gives the same lower bound if one defines a best-equilibrium
selection value instead of taking the supremum over equilibria.

## Proof of Theorem D

Take active players \(1,2\) and dummies \(3,4\). For every nonempty coalition
\(S\), define

\[
r_1(S)=
\begin{cases}
-1,&\{1,2\}\subseteq S,\\
1,&\text{otherwise},
\end{cases}
\qquad r_2(S)=-r_1(S),                                \tag{22}
\]

and for each dummy \(d\), put

\[
r_d(S)=
\begin{cases}
-1,&d\in S,\\
0,&d\notin S.
\end{cases}                                          \tag{23}
\]

All rewards lie in \([-1,1]\).  With both dummies fixed to Never, the active
two-date timing game is the zero-sum game below.  Its canonical mixed law,
together with the two dummy Never laws, is an exact full-game Nash source.
It is not the unique full-game Nash: the checked pure profile
\((\mathsf{Never},0,1,\mathsf{Never})\) is distinct and is also Nash because
the dummy-only terminal rows change the active incentives.

The active zero-sum matrix is

\[
\begin{pmatrix}
-1&1&1\\
1&-1&1\\
1&1&0
\end{pmatrix}.                                       \tag{24}
\]

Its unique active minimax law for each player is \((1/4,1/4,1/2)\), with value
\((1/2,-1/2)\). To see uniqueness, a row law
\((x_0,x_1,x_N)\) has values
\(1-2x_0,1-2x_1,1-x_N\) against the three pure columns. Guaranteeing at least
\(1/2\) forces \(x_0\le1/4,x_1\le1/4,x_N\le1/2\);
their sum forces equality. The dual argument is identical.

Keep the corresponding date-zero hazard \(1/4\) and conditional date-one
hazard \(1/3\), keep the dummies Continue through the prefix, and append an
arbitrary product behavioral tail after joint survival. Let
\(g\in[-1,1]\) be player 1's conditional tail payoff. Joint active survival
has probability \(1/4\), and the active coordinates are zero-sum, so

\[
U_1=\frac12+\frac g4,\qquad
U_2=-\frac12-\frac g4.                               \tag{25}
\]

For a deterministic suffix quit time \(t\), player 1's value is

\[
1-2c_t,
\]

where \(c_t\) is the probability that player 2 first collides with that quit
time.  The quantity \(c_t\) is bounded by player 2's own stopping-law atom at
\(t\), so \(c_t\to0\), including for arbitrary infinite-support tails and a
positive Never atom.  Hence these pure-time values converge to one.  Reward
normalization bounds every deviation value above by one, so the unrestricted
best-response cap is exactly one; no maximizing time is required. Therefore

\[
B_1-U_1\ge1-\left(\frac12+\frac g4\right)
=\frac12-\frac g4\ge\frac14.                         \tag{26}
\]

This lower bound uses one legal pure-time deviation and hence applies to the
full behavioral cap.

For the global boundary, fix an integer \(L\ge1\), discard the prefix, and let
both active players use independent uniform planned times on \(L\) finite
dates; let both dummies Never. A tie has probability \(1/L\). Player 1's
payoff is \(1-2/L\) and its
best value is one, so its debt is \(2/L\). Every pure time of player 2 inside
the window gives its prescribed value \(-1+2/L\); times outside and Never are
worse. Dummies have zero debt. Thus total unrestricted exploitability is
exactly

\[
\frac2L\longrightarrow0.                             \tag{27}
\]

## Boundary tests

- \(R=0\), nonpositive singleton rewards, zero event masses, pure Nash
  coordinates, and exact Never atoms require no division or conditioning.
- At \(K=1\) and \(K=2\), the formula recovers the independently reviewed
  constants \(2R/3\) and \(R/2\).
- The positive part in (11) prevents the false inference
  \(d_i\le L-V_t\) when the raw difference is negative.
- The deadline count is literal: \(K\) finite dates are
  \(0,\ldots,K-1\), and \(h_u\) occurs exactly \(u\) times in the double sum.
- At hierarchy level 60, only this midpoint certificate fails; no positive
  lower value is claimed.
- The hard-tail nonvanishing table has terminal approximation by other
  finite clocks, and Theorem D's table has the exact \(2/L\) escape.
- Theorem D preserves a two-date prefix, not the complete original stopping
  laws: the former Never mass is reopened as survival into the suffix.

## Source correspondence and novelty

The checked general finite-game Nash producer is
KernelGame.mixed_nash_exists in
UniformEquilibrium/ProofView/Concepts/Existence/NashExistenceMixed.lean.

The unrestricted cap reduction is
sSup_range_quittingTerminalPayoff_update_eq_pureTime in
UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean.

The closest checked hard-deadline interfaces are
QuittingFiniteDeadlineNashProfile,
quittingRootSequencePureTimeTerminalValue_late_sub_none_eq, and
QuittingFiniteDeadlineNashProfile.semanticDebt_le_escapeCharge in
UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFiniteDeadlineNashEscalation.lean.
They consume a supplied deadline profile and expose its late escape; they do
not prove the table-uniform function \(f_K\).

The actual finite-clock and hierarchy sources are
quittingFiniteClockSemanticReachable_eq_range_fold,
quittingFiniteClockSemanticReachable_isCompact,
quittingFiniteClockSemanticReachable_mono,
quantileClockSupport, and quantileClockRadius in
Research/Quitting/EscapeAwareQuantileClockHierarchy.lean. The ordinary
hierarchy theorem is
[Escape-aware quantile-clock hierarchy](ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md).
A checked lower-value corollary should retain
HasEscapeAwareQuantileClockCompression reward until that ordinary input is
integrated.

The exact lower regression for Theorem C was independently reviewed in
[CODEX_EULER's review](../feedback/CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING__BY_CODEX_EULER.md).
A narrow declaration and note search found no existing \(f_K\), exact
third-date constant, worst-table quarter limit, or fixed-prefix arbitrary-tail
barrier. No external paper is used beyond finite-game Nash existence already
represented by the checked declaration.

## Adapter and consumer

The arbitrary source for Theorem A is any bounded finite reward table.
Finite mixed-Nash existence supplies the whole \(K\)-date planned-time law;
the hazard realization is a literal product behavioral profile. Pure-time
extremality converts its finite Nash inequalities into an unrestricted
terminal semantic bound.

The hierarchy consumes the actual three-date semantic pair and its diagonal
midpoint, proving (5). The reviewed unique-equilibrium table consumes the
general upper estimate into the exact architecture ceiling (6). Theorem D is
an exact negative boundary for suffix-only repair behind one fixed prefix,
and (27) demonstrates why the same table is not a terminal-gap example.

## Lean handoff

A narrow formalization should proceed in four modules.

1. Define the finite planned-time KernelGame with action type
   Fin \(K\) plus Never, invoke KernelGame.mixed_nash_exists, and prove the
   literal hazard realization including zero remaining mass.
2. Define \(a,h_t,V_t,V_N,L\), prove (10)--(12), sum the finite inequalities,
   and derive (15). Then use
   sSup_range_quittingTerminalPayoff_update_eq_pureTime for the unrestricted
   cap.
3. Formalize the \(K=3\) scalar maximum and hierarchy midpoint separately.
   Keep HasEscapeAwareQuantileClockCompression explicit if the checked
   lower-value API requires it.
4. Define the two rational Fin4 regression tables separately: Miner's
   hard-deadline lower family for Theorem C, and (22)--(23) for Theorem D.
   For Theorem D, prove the canonical source is Nash, record the distinct
   second Nash, then define the fixed prefix and quantify over every
   behavioral product tail.

No desired debt estimate or tail barrier should be introduced as a structure
field.

## Scope and nonclaims

The packet does not prove terminal approximation, a uniform-equilibrium
payoff, or a positive terminal gap. Theorem A re-solves the complete timing
game at every deadline; it does not append a date to a fixed earlier Nash law.
Theorem C rules out vanishing error only for exact hard-zero-tail Nash
selection. Theorem D preserves two early hazards, not complete stopping laws,
and rules out convergence for every behavioral suffix behind that one prefix.
It does not preclude one fixed improvement below \(1/2\).

The packet gives no positive hierarchy certificate at level 60. It does not
close the Fin4 hard residual or the source-preserving soft-tail problem.

## Formalization record

The packet is formalized at its corrected scope in the following checked
modules.

- `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingNashDebt.lean`
  constructs fresh finite-deadline timing Nash profiles, proves the universal
  scalar factor and debt bound, identifies the exact three-date maximum
  `20 - 8 * sqrt 6`, proves it is strictly below `5/12`, and proves the
  rational `24/59` semantic producer.
- `Research/Quitting/FiniteDeadlineTimingNashDebtHierarchy.lean` consumes the
  actual three-date profile in the escape-aware hierarchy and proves
  `escapeAwareQuantileClockLower_finFour_normalized_eq_zero_of_le_fiftyNine`.
- `UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashWorstCase.lean`
  proves
  `tendsto_finiteDeadlineTimingNashWorstExploitability_succ_quarter`, the exact
  worst-table limit in Theorem C.
- `UniformEquilibrium/Diagnostics/Quitting/FixedPrefixArbitraryTailBarrier.lean`
  proves `quarter_le_behavioralTailRepairValue` over every behavioral suffix,
  not only finite-support tails.
- `UniformEquilibrium/Diagnostics/Quitting/FixedPrefixSameTableGlobalComparison.lean`
  proves exact same-table exploitability `2/L`, its convergence to zero, and
  the fixed target uniform-equilibrium payoff.
- `UniformEquilibrium/Diagnostics/Quitting/FixedPrefixTimingNashNonuniqueness.lean`
  proves the canonical prefix source is Nash, constructs the distinct Nash
  `(Never,0,1,Never)`, and proves
  `prefixTimingGame_not_existsUniqueNash`.

Evidence seals are `M`, `L`, `A`, and `C`: the ordinary mathematics passed
both unrestricted-strategy reviews; Lean checks the finite-deadline bound,
exact constants, worst-table limit, and fixed-prefix statements; each result
starts from a literal finite timing law or behavioral suffix on the displayed
game; and the actual profiles are consumed by the hierarchy, all-tail repair
value, exact terminal exploitability, and fixed-target uniform-payoff
interfaces.

Theorem D retains the canonical source and its prefix, not full-game
uniqueness.  No positive hierarchy value at level `60`, positive all-profile
terminal gap, counterexample, CAD/search completeness, or source-preserving
soft-tail construction is claimed.
