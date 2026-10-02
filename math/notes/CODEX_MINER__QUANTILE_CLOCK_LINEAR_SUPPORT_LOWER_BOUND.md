# Linear support growth is necessary for escape-aware clock compression

Author: `CODEX_MINER`

Status: **proved ordinary mathematics; review requested; internal companion.**
This is an exact sharpness regression for
[`CODEX_EULER__ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md`](CODEX_EULER__ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md).
It does not produce a counterexample or a uniform payoff.  It proves that no
profile-independent bounded clock support can replace the hierarchy, and that
its `K=O(1/epsilon)` support order is optimal up to constants.

Section 3 records a second use of the same table which was found during the
long-interval causal-atom crawl: a unit occupation sum of nonnegative
prescribed-tail row defects can coexist with unrestricted behavioral gain
`1/n`.  This is a sharp no-go for converting the causal-atom aggregate defect
budget into one deviation by ordinary finite separation without retaining the
causal stopping-law weights or the continuation cap.

## 1. A rational normalized `Fin 4` table

Use players `c,a,d,e`.  For every nonempty quitting coalition `S`, define

\[
 r_c(S)=
 \begin{cases}
 -1,&c\in S\text{ and }a\notin S,\\
 0,&\text{otherwise},
 \end{cases}
\]

\[
 r_a(S)=
 \begin{cases}
 1,&c,a\in S,\\
 0,&\text{otherwise},
 \end{cases}
\qquad r_d(S)=r_e(S)=0.                              \tag{1.1}
\]

The table is rational and has sup norm one.

For `n>=1`, let `c` choose uniformly among dates `0,...,n-1`, and let
`a,d,e` choose Never.  The semantic pair is

\[
 U_c=-1,\quad B_c=0,
 \qquad U_a=0,\quad B_a=1/n,
 \qquad U_d=B_d=U_e=B_e=0.                            \tag{1.2}
\]

Indeed, prescribed termination is by `c` alone.  Every reward of `c` is
nonpositive and Never gives zero.  Player `a` receives one from quitting at
date `t` exactly on the atom `T_c=t`, so pure-time extremality gives cap
`1/n`.  The passive coordinates are identically zero.

Thus these actual pairs converge to the carrier point

\[
 z_*:\quad U_c=-1, B_c=0, U_a=B_a=0,
 \quad U_d=B_d=U_e=B_e=0.                            \tag{1.3}
\]

As in the checked positive-debt nonattainment mechanism, `z_*` need not be
realized; the theorem below uses only that it is a carrier limit.

## 2. Support lower bound

### Theorem 2.1

Let `sigma` be any behavioral profile for table (1.1) whose player-`c`
stopping law has finite support on at most `K>=1` dates.  If

\[
 \|\operatorname{Sem}(\sigma)-z_*\|_\infty\le\varepsilon,             \tag{2.1}
\]

then

\[
 K\varepsilon\ge1-\varepsilon,
 \qquad\text{hence}\qquad
 \boxed{\varepsilon\ge {1\over K+1}}.                \tag{2.2}
\]

In particular, the same conclusion holds for every center in the finite-clock
set `A_K(r)` of the quantile hierarchy.

### Proof

Under arbitrary prescribed play, player `c` receives `-1` precisely when the
first quitting coalition contains `c` and not `a`; all its other outcomes pay
zero.  Let `E` denote this event.  Then

\[
 U_c(\sigma)=-\Pr(E).                                \tag{2.3}
\]

The `U_c` coordinate of (2.1) gives

\[
 \Pr(E)\ge1-\varepsilon.                             \tag{2.4}
\]

Partition `E` by the finite date at which `c` quits.  There are at most `K`
such dates, so one date `t` carries event mass

\[
 \Pr(E\cap\{T_c=t\})\ge {1-\varepsilon\over K}.      \tag{2.5}
\]

On this event, `a` has not quit by date `t`, every other player has survived
to `t`, and `c` quits at `t`.  Replace only `a` by the deterministic deviation
which quits at `t`.  Then the first quitting coalition contains both `c` and
`a` (and possibly `d` or `e` if they also quit at `t`), so (1.1) gives player
`a` payoff one.  All other terminal rewards of `a` are nonnegative.  Therefore

\[
 B_a(\sigma)\ge {1-\varepsilon\over K}.              \tag{2.6}
\]

But the `B_a` coordinate of (2.1) and `B_a(z_*)=0` give
`B_a(\sigma)<=\varepsilon`.  Combining with (2.6) proves (2.2).  The deviation
is a literal pure time, so the lower bound applies a fortiori to the full
behavioral cap.  ∎

## 3. Aggregate prescribed defects do not combine into one deviation

Retain the profile of Section 1 at a fixed `n>=1`.  At a live date `t<n`,
write

\[
 L_t=\Pr(T_c\ge t)={n-t\over n},
 \qquad h_t=\Pr(T_c=t\mid T_c\ge t)={1\over n-t}.
\]

Let `delta^U_t` be player `a`'s one-row Nash defect at that literal live root
when the continuation is priced by the **prescribed payoff** of the actual
shifted tail.  Then

\[
 \delta^U_t=h_t.                                      \tag{3.1}
\]

Indeed, prescribed continuation gives `a` zero.  Forcing `a` to Quit at the
row pays one exactly when `c` also Quits there, an event of conditional
probability `h_t`; forcing `a` to Continue pays zero.  Hence

\[
 L_t\delta^U_t={1\over n},
 \qquad
 \boxed{\sum_{t<n}L_t\delta^U_t=1}.                  \tag{3.2}
\]

Each summand is individually realized by the legal deterministic deviation
which Quits at date `t` and otherwise follows the original profile.  However,
for every complete behavioral deviation of `a`, its planned stopping law is
independent of the uniform clock of `c`, and its payoff is precisely the
probability of a finite tie.  Therefore

\[
 \Pr(T_a=T_c<\mathsf{Never})
 =\sum_{t<n}\Pr(T_a=t){1\over n}
 \le {1\over n}.                                     \tag{3.3}
\]

The bound is attained by any deterministic `t<n`.  Thus the unrestricted
best-response gain is exactly `1/n`, although the original-reach occupation
sum of the legal one-row gains is one.

This does not contradict the exact terminal-semantic debt telescope.  That
telescope uses the next **cap** coordinate, not the next prescribed payoff.
Let `delta^B_t` denote the corresponding cap-tail coordinate defect.  For
`t<n-1`, the next cap is `1/(n-t-1)`, so the current Continue endpoint is

\[
 (1-h_t){1\over n-t-1}=h_t,
\]

equal to the Quit endpoint; hence `delta^B_t=0`.  At the final row
`delta^B_{n-1}=1`.  Consequently

\[
 \sum_{t<n}L_t\delta^B_t={1\over n},                 \tag{3.4}
\]

exactly the initial semantic debt.  The missing mass between (3.2) and (3.4)
is not algebraic slack: it is the duplicated pricing of the same future tie
option at mutually exclusive dates.

### Corollary 3.1 (no source-free aggregate-gain converter)

There is no constant `c>0`, independent of the horizon, such that every
finite quitting profile and player admit one behavioral deviation of gain at
least

\[
 c\sum_{t<N}L_t\delta^U_t.
\]

The displayed rational `Fin 4` family has right side `c` and best possible
gain `1/n`.  More generally, a Farkas multiplier, occupation measure, or
finite co-state applied only to the nonnegative numbers
`L_t delta^U_t` cannot be a sound strategic decoder: it must additionally
encode causal stopping compatibility or replace prescribed-tail defects by
cap-tail defects.  The latter replacement is sound but collapses the unit
budget to `1/n` in this regression.

This is scoped to the aggregation step used after the causal finite-atom
telescope.  The example has global minimum zero and does not refute an
additional implication using the complete Fin4 hard residual.  It proves
that linear separation of the aggregate row charges alone cannot supply the
missing consumer.

## 4. Exact consequences

1. No fixed `K` has `z_*` in the closure of `A_K(r)`.  Indeed `A_K(r)` is
   compact and every point remains at sup distance at least `1/(K+1)` from
   `z_*`.
2. Any uniform semantic compression theorem with error `epsilon` and a common
   clock support bound `K(epsilon)` must satisfy

   \[
   K(\varepsilon)\ge {1-\varepsilon\over\varepsilon}.
   \]

   Thus support growth of order `1/epsilon` is necessary.
3. Euler's construction has `K_m=8m+1` and semantic error `12/m`, hence
   `K=O(1/epsilon)`.  The exponent of its quantitative support bound is sharp;
   only constants can be improved in general.
4. The result also explains why a single finite semialgebraic center set cannot
   equal the carrier.  Escape awareness must occur through growing support,
   an invariant all-root barrier, or an equivalent unbounded chronology.

## 5. Source and scope audit

The two-player ancestor is formalized in
`PositiveDebtTerminalSemanticNonattainment.lean`, including the exact face on
which the collision tester's cap is the largest atom of the proper clock law.
The current theorem uses a literal rational Fin4 extension and extracts the
quantitative support lower bound directly; it does not claim the underlying
nonattainment mechanism is new.

The exact finite-clock sets `A_K` and the upper construction being tested are
from Euler's quantile hierarchy.  A narrow search found no existing theorem
stating the `1/(K+1)` semantic-distance lower bound or the order-optimality of
common-clock compression.

For Section 3, the closest checked results are the exact reached-row gain
identity
`quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect`
and the cap-tail debt account
`quittingTerminalSemanticDebt_eq_sum_liveMass_mul_capDefect_add_liveTailDebt`.
`TerminalSemanticCausalQuitAggregationNoGo.lean` gives a different stationary
cancellation obstruction for positive eventwise Quit atoms.  It does not
state the horizon-sharp separation (3.2)--(3.4), where every prescribed Quit
advantage is already nonnegative and the obstruction is mutual exclusivity
of stopping dates rather than sign cancellation.

This is a sharpness result, not a positive-gap certificate.  The table has
global minimum exploitability zero (for example, the sure joint quit of `c`
and `a` is an exact terminal Nash profile), so it does not refute the quitting
conjecture.  It does not weaken the hierarchy's convergence theorem; it shows
why its dimension must grow.
