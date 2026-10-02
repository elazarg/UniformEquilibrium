# Finite-watchdog and geometric-security no-go results

Author: `CHATGPT_EXTERNAL`

Status: `REVISED AFTER INDEPENDENT REVIEW; INTERNAL; DOES NOT ANSWER THE PARENT QUESTION`

## Current result

This note responds to
[`../questions/INCENTIVE_GADGET.md`](../questions/INCENTIVE_GADGET.md). It does
not provide the requested complete rational reward table and fixed positive
all-behavior terminal exploitability gap. It also does not prove a universal
existence theorem excluding every such table.

The contribution is narrower:

1. every finite preselected family of watchdog deviations has an ordinary
   behavioral profile immune to all of those watchdogs;
2. a geometric strategy has a complete profile-independent security theorem
   under an exact family of toggle inequalities;
3. a late geometric splice quantitatively suppresses joint Never mass, in
   fact without the security hypotheses;
4. profile-independent security inequalities cannot alone force an impossible
   product-clock incidence pattern, with a linear upper bound for
   antisymmetric rows; and
5. a natural pair-local synchronization table has an explicit exact
   stationary geometric equilibrium.

These results eliminate a larger class of prospective gadget architectures,
but the profile-dependent, unbounded-time incentive cycle required by the
question remains open.

All results below are ordinary mathematics not checked in Lean. The review in
[`../feedback/CHATGPT_EXTERNAL__FINITE_WATCHDOG_GEOMETRIC_SECURITY_NO_GO__BY_CODEX_PASCAL.md`](../feedback/CHATGPT_EXTERNAL__FINITE_WATCHDOG_GEOMETRIC_SECURITY_NO_GO__BY_CODEX_PASCAL.md)
accepted the mathematics after the explicit repairs incorporated here. This
does not change the export status: the packet remains internal because it does
not answer the parent question under either accepted answer standard.

## Exact parent question and logical level

The parent question asks for one finite rational quitting game in which every
sufficiently accurate terminal approximate Nash profile forces two designated
strict-first pair atoms `a` and `b` above a common positive threshold while
forcing all remaining first outcomes plus Never, `ell`, below twice that
threshold. Together with the reviewed independent-clock inequality

\[
\ell^2\ge 4ab,
\]

such a table would give one fixed positive unilateral terminal gain against
every unrestricted behavioral profile.

Accordingly, the requested table would be a genuine negative resolution for
that finite quitting game. Conversely, a theorem excluding every possible
table of this kind by producing arbitrarily accurate ordinary equilibria would
settle the corresponding approximate-equilibrium existence question. The
results below exclude only specified architectural classes. A failed gadget
search is not a negative answer.

## Sources inspected

- [`../questions/INCENTIVE_GADGET.md`](../questions/INCENTIVE_GADGET.md),
  including its accepted positive and negative answer standards.
- The reviewed clock inequality in
  [`CODEX_CEDAR__INDEPENDENT_CLOCK_TOGGLE_GADGET.md`](CODEX_CEDAR__INDEPENDENT_CLOCK_TOGGLE_GADGET.md).
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime`
  (`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`). This
  checked declaration identifies the fixed-opponent behavioral best-response
  supremum with the supremum over deterministic quit times, including Never.
- `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  (`UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`). This checked
  declaration confirms that a fixed positive terminal gap against every
  behavioral profile is exactly the negative semantic endpoint.
- `collisionMass_logarithmicBlock_le_sq`
  (`UniformEquilibrium/Quitting/AbsorptionPath/LogarithmicBlockDiscretization.lean`).
  This checked quadratic collision estimate is relevant to diffuse schedules,
  but it is not used in the proofs below.
- Ashkenazi-Golan, Krasikov, Rainer, and Solan, *The APS approach for
  undiscounted quitting games*, International Journal of Game Theory 55,
  article 19 (2026),
  [publisher page](https://link.springer.com/article/10.1007/s00182-026-00982-6),
  especially the introduction and Section 2.1. The paper states that existence
  of limit subgame-perfect equilibrium payoffs is not known for quitting games
  with at least four players, and its own characterization covers a restricted
  absorption-path subclass. This source does not by itself verify the broader
  wording that every formulation of ordinary approximate-equilibrium
  existence is unknown. The mathematical results below do not depend on that
  literature-status sentence.
- Proposition 26 of
  [`CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`](CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md)
  is the direct finite-calendar precursor to Theorem 1. Theorem 1 uses the
  same finite-game mechanism for arbitrary finite, player-dependent menus of
  complete behavioral strategies rather than one common finite calendar.
- Proposition 21 of that note gives the fixed-calibrator product-law escape
  and already records the general simultaneous-security-profile obstruction.
  Theorem 2 supplies the stronger single-player guarantee against arbitrary
  opponent clocks under the geometric toggle inequalities; Section 4 reuses
  the general simultaneous-security observation rather than claiming it as
  new.
- Proposition 39 of that note is the related late-solo refusal account. It
  controls opponent-Never mass through a prescribed-over-Never premium,
  whereas Theorem 3 below isolates joint Never mass directly by a late splice.
- Proposition 6 of
  [`CODEX_CEDAR__INDEPENDENT_CLOCK_TOGGLE_GADGET.md`](CODEX_CEDAR__INDEPENDENT_CLOCK_TOGGLE_GADGET.md)
  already gives the uniform-coalition-law feasibility obstruction for finite
  indicator-flow networks. Theorem 4 applies the same uniform law to general
  antisymmetric secured-payoff rows and records the corresponding LP bound.
- The narrow search found no prior statement of the pair-local table in
  Theorem 5. These overlap findings supersede the initial, overly broad
  novelty claim for the five-theorem packet.

## 1. No finite watchdog family can prove an all-profile gap

Let `G` be any finite quitting game. For each player `i`, choose any nonempty
finite collection of behavioral strategies

\[
\mathcal D_i=\{\tau_i^1,\ldots,\tau_i^{m_i}\}.
\]

The collection may contain fixed quit times, geometric clocks, cutoffs,
prescribed join deviations, tail switches, or arbitrary finite-state plans.

### Theorem 1: finite-watchdog impossibility

There is an ordinary behavioral profile `sigma` such that

\[
U_i(\tau_i,\sigma_{-i})\le U_i(\sigma)
\qquad
(i\in I,\ \tau_i\in\mathcal D_i).
\]

### Proof

Form the finite strategic-form game whose pure strategies for player `i` are
the elements of `D_i`, with payoff given by the quitting game's terminal
payoff. Nash's theorem supplies a mixed equilibrium of this finite game.

Independently drawing one behavioral strategy from each player's equilibrium
mixture produces a mixture of quit-time laws. A mixture of laws on

\[
\mathbb N\cup\{\infty\}
\]

is again one quit-time law, and every such law has a behavioral hazard
representation

\[
q_t=\Pr(T=t\mid T\ge t).
\]

Replacing each player's initial mixture by this hazard representation preserves
the independent joint quit-time law, hence every terminal payoff appearing in
the finite-game Nash inequalities. The finite-game equilibrium is therefore
an ordinary behavioral profile of the original quitting game, and its Nash
inequalities are exactly the displayed inequalities. ∎

Consequently, a positive exploitability-gap proof cannot reduce all profitable
deviations to any finite list of preselected watchdog strategies. The
profitable pure time must depend on the candidate profile, and the possible
witness times must be genuinely unbounded. Adding finitely many claimant ranks
or blocker ranks does not change this conclusion.

This theorem does not exclude a finite reward table whose profitable deviation
is selected from an infinite, profile-dependent family.

## 2. A parameterized geometric-security lemma

Fix a player `i`, let

\[
s_i=r_i(\{i\}),
\]

and choose a rational `theta` with `0<theta<1`. Suppose that for every nonempty
opponent coalition `C` contained in `I\{i}`,

\[
\boxed{
\theta r_i(C\cup\{i\})+(1-\theta)r_i(C)\ge0
}
\tag{1}
\]

and `s_i>=0`.

Let player `i` use the geometric quit time

\[
\Pr(G_\theta=t)=\theta(1-\theta)^t.
\]

### Theorem 2: geometric toggle security

Against every profile of the opponents,

\[
U_i(G_\theta,\sigma_{-i})\ge0.
\]

### Proof

First condition on deterministic opponent clocks. Let `tau` be their earliest
finite time and `C` their earliest coalition. For finite `tau`,

\[
\begin{aligned}
U_i
={}&
\Pr(G_\theta<\tau)s_i
+\Pr(G_\theta=\tau)r_i(C\cup\{i\})\\
&+\Pr(G_\theta>\tau)r_i(C)\\
={}&
\bigl(1-(1-\theta)^\tau\bigr)s_i\\
&+(1-\theta)^\tau
\bigl[\theta r_i(C\cup\{i\})+(1-\theta)r_i(C)\bigr]
\ge0.
\end{aligned}
\]

If all opponents choose Never, `G_theta` terminates alone and gives
`s_i>=0`. Averaging over arbitrary independent opponent clocks proves the
result. ∎

The antisymmetric construction is the special case

\[
\theta=\tfrac12,
\qquad
r_i(C\cup\{i\})=-r_i(C).
\]

## 3. A late geometric splice quantitatively eliminates joint Never

The geometric strategy can be spliced after an arbitrary cutoff rather than
used from date zero. The security hypotheses of Theorem 2 are not needed for
this limiting argument: boundedness makes every adverse finite-opponent tail
event vanish as the cutoff tends to infinity.

### Theorem 3: Never-mass bound

In any finite quitting game with zero payoff at Never, fix a player `i` with
solo payoff `s_i=r_i({i})>0`. For every behavioral profile `sigma`,

\[
B_i(\sigma)-U_i(\sigma)
\ge
s_i\Pr_\sigma(T_j=\infty\text{ for every }j).
\tag{2}
\]

Hence every terminal `epsilon`-Nash profile satisfies

\[
\boxed{
\Pr_\sigma(\mathrm{Never})\le \frac{\varepsilon}{s_i}.
}
\tag{3}
\]

### Proof

Represent `sigma` by independent quit times `(T_j)_(j in I)`, and write

\[
T_{-i}:=\min_{j\ne i}T_j.
\]

Fix any `theta` in `(0,1)`. For a cutoff `N`, let `sigma_i^(N)` follow
`sigma_i` at every date strictly before `N` and, conditional on survival to
`N`, discard its old residual clock and use an independent shifted geometric
clock `N+G_theta`.

Couple the original and spliced profiles so that they use the same clocks and
actions before `N`. Their terminal outcomes can differ only after survival to
`N`, and this difference splits into two disjoint opponent events:

\[
E_N:=\{N\le T_{-i}<\infty\},
\qquad
E_\infty:=\{T_{-i}=\infty\}.
\]

Because the reward table is finite, choose `M` so that the absolute difference
between any two terminal rewards of player `i` is at most `M`. On `E_N`, the
payoff difference is bounded below by `-M`; moreover

\[
\Pr(E_N)\longrightarrow0,
\]

since the events `E_N` decrease to the empty event.

On `E_infinity`, there are three cases. If the original player quits before
`N`, the profiles coincide. If its original quit time is finite and at least
`N`, both the original and spliced profiles eventually terminate at `{i}` and
pay `s_i`. If the original player also Never quits, the old profile pays zero
and the geometric splice quits almost surely and pays `s_i`. Consequently,
the contribution of `E_infinity` to the gain is exactly

\[
s_i\Pr_\sigma(T_j=\infty\text{ for every }j).
\]

It follows that

\[
\begin{aligned}
&U_i(\sigma_i^{(N)},\sigma_{-i})-U_i(\sigma)\\
&\qquad\ge
s_i\Pr_\sigma(T_j=\infty\text{ for every }j)-M\Pr(E_N),
\end{aligned}
\]

and hence

\[
\liminf_{N\to\infty}
\bigl(U_i(\sigma_i^{(N)},\sigma_{-i})-U_i(\sigma)\bigr)
\ge
s_i\Pr_\sigma(T_j=\infty\text{ for every }j).
\]

Every `sigma_i^(N)` is a legal behavioral deviation. Taking the best-response
supremum gives (2), and the terminal `epsilon`-Nash inequality gives (3). ∎

Thus joint Never mass can be suppressed without a separate immediate-Quit
claimant, without the toggle-security inequalities, and without thereby
creating a sure-exit calibrator core. This is a joint-Never estimate, not the
opponent-Never estimate in Gauss's Proposition 39.

## 4. Universal-security constraints cannot force the clock contradiction

Suppose player `i` has a strategy `g_i` satisfying

\[
U_i(g_i,\rho_{-i})\ge c_i
\qquad\text{for every }\rho_{-i}.
\tag{4}
\]

Then playing all the `g_i` simultaneously gives an ordinary product profile
`g` satisfying

\[
U_i(g)\ge c_i
\qquad(i\in I).
\tag{5}
\]

Therefore inequalities of the form `U_i>=c_i-epsilon`, obtained solely from
profile-independent security strategies, cannot imply an event condition
violated by every product clock profile. In particular, they cannot by
themselves imply

\[
a\ge\alpha,
\qquad
b\ge\alpha,
\qquad
\ell<2\alpha,
\]

because the simultaneous security profile itself is subject to
`ell^2>=4ab`. Some essential inequality must instead arise from a best
response selected using the actual opponent clock law.

There is also a linear obstruction in the symmetric geometric case.

### Theorem 4: `1/(2^n-1)` bound for antisymmetric security rows

Assume there are `n` players and, for every player `i` and every nonempty
coalition `C` contained in `I\{i}`,

\[
r_i(C\cup\{i\})=-r_i(C),
\]

and assume

\[
r_i(\{i\})\ge0.
\tag{6}
\]

Fix a nonempty coalition `A`. Let `p` range over probability laws on the
`2^n-1` nonempty coalitions, with no Never mass in this finite-dimensional
statement. If every such `p` satisfying all secured-payoff inequalities

\[
\sum_S p(S)r_i(S)\ge0
\qquad(i\in I)
\tag{7}
\]

satisfies `p(A)>=alpha`, then

\[
\boxed{
\alpha\le\frac1{2^n-1}.
}
\tag{8}
\]

For four players, `alpha<=1/15`.

### Proof

First observe that the constraint system is nonempty. The uniform law

\[
p_{\mathrm{unif}}(S)=\frac1{2^n-1}
\qquad(\varnothing\ne S\subseteq I)
\]

is feasible. Indeed, for a fixed player `i`, pair every nonempty
`C subseteq I\{i}` with `C union {i}`. Toggle antisymmetry cancels every such
pair, while the only unpaired nonempty coalition is `{i}`. Therefore

\[
\sum_{\varnothing\ne S\subseteq I}r_i(S)=r_i(\{i\})\ge0,
\]

so the uniform law's expected payoff in coordinate `i` is

\[
\frac{r_i(\{i\})}{2^n-1}\ge0.
\]

Applying the assumed implication directly to this feasible law already gives

\[
\alpha\le p_{\mathrm{unif}}(A)=\frac1{2^n-1}.
\]

For completeness, the corresponding LP certificate has the same bound. The
primal program is

\[
\begin{aligned}
\text{minimize }&p(A)\\
\text{subject to }&p(S)\ge0,\quad \sum_Sp(S)=1,\\
&\sum_Sp(S)r_i(S)\ge0\quad(i\in I).
\end{aligned}
\]

It is feasible by the uniform law and compact because it is a closed subset
of the finite coalition simplex. Its dual has variables `lambda_i>=0` and a
free scalar `y`. Finite-dimensional strong duality says that the asserted
lower bound on the primal optimum provides `y>=alpha` such that, for

\[
f(S)=\sum_i\lambda_i r_i(S),
\]

one has

\[
f(S)+y\le \mathbf 1_{\{S=A\}}.
\tag{9}
\]

Summing (9) over all `2^n-1` nonempty coalitions yields

\[
(2^n-1)y\le1,
\]

because every summed `f` coordinate is nonnegative by the cancellation
identity. Together with `y>=alpha`, this recovers (8). ∎

This bound is far below the `alpha>1/4` threshold that would make the separate
`ell` watchdog unnecessary.

## 5. Pair-local synchronization incentives have a geometric escape

Let the four players be paired by

\[
p(1)=2,
\quad p(2)=1,
\quad p(3)=4,
\quad p(4)=3.
\]

Fix rational numbers `E>0>T` and define, for every nonempty coalition `S`,

\[
r_i(S)=
\begin{cases}
E,&i\in S,\ p(i)\notin S,\\
T,&i,p(i)\in S,\\
0,&i\notin S.
\end{cases}
\tag{10}
\]

Membership of the other pair is irrelevant. Put

\[
h=\frac{E}{E-T}\in(0,1).
\]

### Theorem 5: exact geometric equilibrium

The stationary profile in which every player Quits at every live date with
probability `h` is an exact terminal Nash equilibrium.

### Proof

At every live date, player `i`'s Quit endpoint is

\[
(1-h)E+hT=0.
\]

If `i` Continues, any opponent absorption omits `i` from the terminal coalition
and therefore pays `i` zero. If every opponent Continues, the game returns to
the same live state.

The zero continuation value is not merely a chosen Bellman fixed point. Write
`x=1-h`. Under the three stationary opponents, the probability that all of
them Continue for one more date is `x^3<1`, so their first absorption time is
finite almost surely. Against these opponents, any deterministic finite Quit
time for `i` receives zero: every earlier opponent absorption omits `i`, and
at the selected Quit date the partner's independent current action makes the
Quit endpoint `(1-h)E+hT=0`. Pure Never also receives zero because the
opponents absorb almost surely and omit `i`. Thus every pure quit time,
including Never, pays zero. By fixed-opponent pure-time extremality, every
unrestricted behavioral deviation pays at most zero. The prescribed
stationary strategy also pays zero, so the profile is an exact terminal Nash
equilibrium. ∎

The exact strict-first mass of either designated pair is

\[
a=b=
\frac{h^2(1-h)^2}{1-(1-h)^4}
<\frac1{12}.
\tag{11}
\]

Indeed, at any fixed live date the designated pair Quits and the other pair
Continues with probability `h^2(1-h)^2`, while reaching that date requires all
four players to have Continued at every earlier date. Summing the geometric
series with common ratio `(1-h)^4` gives the displayed formula.

To prove the strict numerical bound, put `x=1-h`, so `0<x<1`. Then

\[
a=\frac{x^2(1-x)}{1+x+x^2+x^3}.
\]

The inequality `a<1/12` is equivalent to

\[
P(x):=13x^3-11x^2+x+1>0.
\]

Here

\[
P'(x)=39x^2-22x+1
\]

and `P` has its only interior local minimum at

\[
x_+=\frac{11+\sqrt{82}}{39}.
\]

Here `P'(x_+)=0`.

The endpoint values are `P(0)=1` and `P(1)=4`. At the critical point, the
identity `39x_+^2-22x_++1=0` gives

\[
P(x_+)=\frac{1664-2132x_+}{1521}.
\]

Since `sqrt(82)<10`, one has `x_+<21/39=7/13`, and therefore

\[
1664-2132x_+>1664-2132\frac7{13}=516>0.
\]

Thus `P` is positive at both endpoints and at its only interior local
minimum, proving `a<1/12`. This equilibrium is therefore nowhere near the
required `1/4` threshold.

## What has been excluded

Taken together with the earlier claimant and sure-exit-core results, these
arguments exclude the following as complete solutions:

- finitely many fixed watchdog deviations;
- any finite all-ranks claimant or blocker menu;
- immediate-Quit outside-option claimants;
- universal geometric-security constraints;
- antisymmetric toggle rows;
- pair-local synchronization penalties; and
- internally stable calibrator cores.

Each exclusion has the exact scope stated in its theorem. None is a theorem
that every finite quitting game has an ordinary approximate equilibrium.

## Remaining obstruction

The earlier concentration lemma says that pair mass `a` exposes some pure date
with mass at least `a^2`. The unresolved point is that this date depends on the
profile and can escape arbitrarily far along a sequence of equilibria of
finite restrictions. Theorem 1 explains why that dependence is unavoidable:
every bounded collection of candidate dates has an exact restricted-Nash
escape.

A successful positive gadget would therefore need a genuinely noncompact
incentive cycle in which an escaping witness time retains a fixed gain after
conditioning on every preceding survival event, while no limiting Never,
stationary-geometric, or sure-exit profile is stable. No such construction is
given here.

## Independent review incorporated

The Pascal review accepted Theorems 1 and 2 and required four explicit
repairs, all now incorporated:

- Theorem 3 now has the full event decomposition and `liminf` bound, and its
  statement records that geometric-security hypotheses are unnecessary.
- Theorem 4 now quantifies the nonempty toggle coalitions exactly, restricts
  `p` to absorbed laws on nonempty coalitions, exhibits the feasible uniform
  law, and states the primal and dual programs. The unsupported word “sharp”
  has been removed.
- Theorem 5 now proves that opponent absorption occurs almost surely, checks
  every pure quit-time boundary including Never, and derives `a<1/12` by an
  exact polynomial argument.
- The source audit now distinguishes the overlaps with Gauss's Propositions
  21, 26, and 39 and Cedar's Proposition 6 from the strengthened statements
  recorded here.

No complete reward-table gap and no universal no-gadget theorem is claimed.
The unresolved issue is not one of these local repairs; it is the missing
profile-dependent noncompact incentive cycle.

## Feedback wanted

1. Can the profile-dependent pure-time witness be made conditionally durable
   without introducing a stationary, sure-exit, or Never escape?
2. Is there a finite table whose reward rows force such a durable unbounded
   witness family while controlling every coalition involving calibrators?
