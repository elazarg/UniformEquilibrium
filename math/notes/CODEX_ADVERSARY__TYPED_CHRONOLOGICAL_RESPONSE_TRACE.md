# Typed chronological response traces

Author: `CODEX_ADVERSARY`  
Date: 2026-08-31  
Status: **proved ordinary mathematics; not Lean-checked; source consequence is compact chronological shadowing, not an executable Fin4 port**

## 1. Question and outcome

The absorption train in
[`NONLOCAL_RECENTERING_ATTACK.md`](../fable/NONLOCAL_RECENTERING_ATTACK.md)
incorrectly tried to turn a car selected from the sum of the actual
absorption law and the four player-deleted laws into one full-profile
kernel.  The independent review
[`NONLOCAL_RECENTERING_ATTACK_REV3__BY_CODEX_ROOT.md`](../feedback/NONLOCAL_RECENTERING_ATTACK_REV3__BY_CODEX_ROOT.md)
gave the decisive counterexample: a player may quit surely at date zero,
while an opponent quits at a drifting date after that player is deleted.

The right question is whether the correctly typed data still admit one
chronologically ordered compactification strong enough to retain both the
terminal law/payoff and all unrestricted caps.

The answer is **yes**.  There is an exact bounded-variation construction:

1. actual first-absorption increments carry the terminal law and prescribed
   payoff;
2. player-`i`-deleted opponent-absorption increments carry player `i`'s cap;
3. away from nonvanishing deleted atoms, the finite Quit values are the solo
   envelope up to a vanishing error; and
4. after charging time by the sum of the actual and all player-deleted stage
   masses, every pure-time response-value sequence has total speed at most
   `4M` on one common clock.

Consequently every sequence, and in fact every **finite family** of source
and counterfactual profiles, has a subsequence on which the labelled actual
laws and continuous response traces converge uniformly on one compact
ordered interval.  The unrestricted cap is exactly the maximum of the
response trace, so maxima commute with the limit.

This proves the cap-assembly statement that the scalar train was trying to
reach, in a stronger finite-family and order-preserving form.  It does **not**
turn a deleted-player car into an actually reached port.  Section 7 gives a
sharp four-player regression showing that even a unit response-square atom
and zero endpoint debt leave actual reach equal to zero.

## 2. Exact one-player ledger

Let `I` be finite, let `sigma` be an arbitrary behavioral profile of a
quitting game, and suppose every terminal reward coordinate has absolute
value at most `M`, where `M>=0`.

Fix player `i`.  Read the profile on its unique live path as a sequence of
product roots.  At date `t`, write

- `c_i(t)` for the probability that every opponent of `i` Continues;
- `a_i(t)=1-c_i(t)` for the one-row opponent-absorption probability;
- `rho_i(0)=1` and `rho_i(t+1)=rho_i(t)c_i(t)` for opponent-only survival;
- `mu_i(t)=rho_i(t)a_i(t)` for the unconditional, player-`i`-deleted
  absorption mass at date `t`;
- `C_i(t)` for the unconditional one-row reward contribution when `i`
  Continues and at least one opponent Quits;
- `V_i(t)` for the one-row expected payoff when `i` Quits surely;
- `s_i=r_i({i})`; and
- `L_i(t)=sum_{u<t} rho_i(u) C_i(u)` for the passive ledger before date `t`.

The finite pure-time value and the solo envelope are

\[
 Q_i(t)=L_i(t)+\rho_i(t)V_i(t),\qquad
 S_i(t)=L_i(t)+\rho_i(t)s_i.
\tag{2.1}
\]

Literal Never has value

\[
 N_i=\lim_{t\to\infty}L_i(t).
\tag{2.2}
\]

The existing checked ledger and pure-time declarations give (2.1)--(2.2)
directly.  The following estimates are elementary consequences:

\[
 |C_i(t)|\le M a_i(t),\qquad
 |V_i(t)-s_i|\le 2M a_i(t).
\tag{2.3}
\]

Therefore

\[
 \begin{aligned}
 S_i(t+1)-S_i(t)
   &=\rho_i(t)\bigl(C_i(t)-a_i(t)s_i\bigr),\\
 |S_i(t+1)-S_i(t)|&\le 2M\mu_i(t),\\
 |Q_i(t)-S_i(t)|&\le 2M\mu_i(t).
 \end{aligned}
\tag{2.4}
\]

Put `chi_i(t)=Q_i(t)-S_i(t)`.  Since
`sum_t mu_i(t)<=1`, equations (2.4) imply

\[
 \begin{aligned}
 |Q_i(t+1)-Q_i(t)|
 &\le 2M\mu_i(t)+2M\mu_i(t)+2M\mu_i(t+1)\\
 &=4M\mu_i(t)+2M\mu_i(t+1),
 \end{aligned}
\tag{2.5}
\]

and hence

\[
 \sum_{t\ge0}|Q_i(t+1)-Q_i(t)|\le 6M.
\tag{2.6}
\]

Thus `Q_i(t)` has a limit.  More precisely,

\[
 \lim_t Q_i(t)=\lim_t S_i(t)=N_i+\rho_i(\infty)s_i,
\tag{2.7}
\]

because `mu_i(t)->0`, hence `chi_i(t)->0`.

Finally, behavioral pure-time extremality gives the exact all-behavior cap
formula

\[
 B_i(\sigma)=\max\left\{N_i,\sup_{t\in\mathbb N}Q_i(t)\right\}.
\tag{2.8}
\]

No stationarity, Nash property, absorption assumption, or sign condition on
the solo payoff is used.

## 3. One common chronological clock

Let `alpha(t)` be the actual probability of first absorption at date `t`.
Define the common stage charge

\[
 d(t)=\alpha(t)+\sum_{i\in I}\mu_i(t).
\tag{3.1}
\]

Every summand is a subprobability law, so

\[
 \sum_t d(t)\le |I|+1.
\tag{3.2}
\]

Define clock vertices

\[
 x(0)=0,\qquad x(t+1)-x(t)=e(t):=d(t)+d(t+1).
\tag{3.3}
\]

Then

\[
 x(\infty):=\lim_t x(t)\le2(|I|+1).
\tag{3.4}
\]

Equation (2.5) gives, simultaneously for every player,

\[
 |Q_i(t+1)-Q_i(t)|\le4M e(t).
\tag{3.5}
\]

If `e(t)=0`, (3.5) says that the two endpoint values agree.  Interpolate
linearly between `Q_i(t)` at `x(t)` and `Q_i(t+1)` at `x(t+1)`.  At
`x(infinity)` use the limit (2.7), keep the path constant up to
`2(|I|+1)`, and on the last unit interval interpolate linearly from that
limit to `N_i`.  This gives a continuous response trace

\[
 F_i^\sigma:[0, 2(|I|+1)+1]\longrightarrow[-M,M]
\tag{3.6}
\]

with Lipschitz constant at most `4M` (the zero-reward case is constant).  Its
defining vertices are
literal chronological pure stopping times, and

\[
 \max_xF_i^\sigma(x)=B_i(\sigma).
\tag{3.7}
\]

Indeed linear interpolation creates no value above its endpoints, the
finite vertices are exactly the `Q_i(t)`, the accumulation vertex is their
limit, and the last segment adds exactly the Never endpoint.

On the same intervals, linearly interpolate every cumulative labelled actual
law

\[
 A_S(t)=\sum_{u<t}\Pr_\sigma(\text{first absorption at }u
                              \text{ by coalition }S)
\tag{3.8}
\]

and every cumulative labelled deleted-`i` opponent law.  Each coordinate
increment is at most `d(t)<=e(t)`, so all these law paths are one-Lipschitz
on the same clock.  Their endpoints are respectively the actual terminal
law and the opponent-only law.  The Never mass is one minus the sum of the
finite actual-law endpoints.

This is the promised typing:

- the `A_S` coordinates are actual-law cars/continuous residue and determine
  `U`;
- the deleted-`i` coordinates and `F_i` determine only `B_i`; and
- all coordinates share order because they use the same literal date `t`
  before the common reparametrization.

## 4. Compactness theorem

### Theorem 4.1 (finite-family typed chronological trace compactness)

Fix a finite player set and a reward bound `M`.  Let `H` be a finite index
set and, for every `n` and `h in H`, let `sigma_n^h` be a behavioral profile
of the same quitting game.  There is a subsequence and one common compact
interval on which, simultaneously for every `h`, every terminal coalition,
and every player:

1. the linearly parametrized labelled actual-law paths converge uniformly;
2. the linearly parametrized labelled deleted-player law paths converge
   uniformly; and
3. the response traces `F_i^{sigma_n^h}` converge uniformly.

The clock is obtained by replacing (3.1) by the sum over `h in H`; its domain
has length at most

\[
 2|H|(|I|+1)+1.
\tag{4.1}
\]

If `F_i^h` is the limiting response trace, then

\[
 \lim_n B_i(\sigma_n^h)=\max_xF_i^h(x).
\tag{4.2}
\]

The endpoints of the limiting actual-law paths give the limiting terminal
law and prescribed payoff.  Hence the complete semantic pairs converge on
the **same subsequence and the same ordered compactification**.

### Proof

For the finite family, the total common stage charge is at most
`|H|(|I|+1)`.  The law paths are uniformly bounded and one-Lipschitz; the
response traces are uniformly bounded by `M` and `4M`-Lipschitz.  There are
only finitely many coordinates.  Arzela--Ascoli and a finite diagonal choice
give simultaneous uniform convergence.  Uniform convergence on a compact
domain implies convergence of maxima, and (3.7) gives (4.2).  Endpoint
evaluation is continuous, so the labelled terminal laws and therefore their
reward moments converge as well.  This proves every assertion.  ∎

The theorem is stronger than extracting convergence of the finite-dimensional
semantic pairs: it retains a common chronological order and an exact
maximizing trace for every unrestricted cap.

## 5. Cars and residue without a false common kernel

At resolution `eta>0`, call date `t` heavy if `d(t)>=eta`.  There are at most
`(|I|+1)/eta` heavy dates.  At a nonheavy date, for every player `i`,

\[
 |Q_i(t)-S_i(t)|\le2M\eta.
\tag{5.1}
\]

Thus the complement of the finitely many heavy rows is exactly the
solo-envelope residue up to `2M eta`.  Letting `eta` decrease to zero yields
the train interpretation:

- a row with nonvanishing actual mass is an **actual absorption car** and
  may carry terminal law/payoff;
- a row with nonvanishing `mu_i` is a **deleted-`i` counterfactual car** and
  may carry the collision correction to `B_i`; and
- everything else converges through the bounded-variation solo-envelope
  trace.

If `alpha_n(t_n)>=kappa>0`, actual reach to `t_n` is at least `kappa`, so the
full pre-car hazard has the usual logarithmic bound.  If instead
`mu_{n,i}(t_n)>=kappa`, only opponent survival satisfies
`rho_{n,i}(t_n)>=kappa`; only the opponents' pre-car hazards have the
logarithmic bound.  There is no bound on player `i`'s own pre-car hazard.

This replaces the false “every car is a full kernel” claim by an exact typed
statement.  It also removes the countably-many-cars supremum problem: the
entire cap, including cars whose labels drift and the Never endpoint, is the
maximum of one uniformly convergent compact trace.

## 6. Consequence for the current Fin4 atom source

The checked source in
`StoppingLaw/VanishingDebtAtomAlternative.lean` supplies a finite family of
profiles: the literal source, its mover-reset endpoint, and the two profiles
obtained by installing one common pure-time observer response.  Apply Theorem
4.1 to this finite family.

Any fixed prescribed terminal payoff-difference atom is an endpoint
difference of two labelled **actual-law** paths, so it survives in the common
trace limit.  Any response-square terminal atom is likewise an endpoint
difference of the two response-profile actual-law paths.  The observer's
unrestricted cap and the selected pure-time value survive simultaneously in
the observer's typed response trace: the selected clock points lie in a fixed
compact interval, so a further subsequence makes them converge, and uniform
trace convergence then transports their values.  Thus separate compactness
selections are unnecessary: terminal atoms, law, payoff, selected responses,
and all caps can be kept on one ordered compact parameter after one
subsequence.

This is a genuine compact chronological-shadowing consequence of the actual
source data.  It is not the Tier-I producer requested in
[`FIN4_TWO_TIER_CHRONOLOGICAL_SHADOWING.md`](../questions/FIN4_TWO_TIER_CHRONOLOGICAL_SHADOWING.md):

- the common clock is a reparametrization of a finite family of actual and
  counterfactual histories, not one behavioral profile;
- a response-square contribution may be diffuse in ordinary dates or may
  lie in a deleted-observer car;
- no actual reach floor follows for that car; and
- the construction supplies no exact Nash--Bellman successor, two fixed
  hazard labels, repeatability, or small-debt seed.

The precise surviving source gain is therefore **co-realized ordered
compactness**, not executable sewing.

## 7. Sharp no-go: zero-debt response car with zero actual reach

The missing actual-reach implication is false even with unit constants.
Use four players `1,2,3,4`.  Let every unmentioned player play Never.  For
each `n>=1`, let the literal source profile have player `1` Quit surely at
date zero and player `2` play Never.  Let the mover-reset target replace
player `2` by sure Quit at date `n`.  Use player `1` as the common-response
observer and let its selected pure response be sure Quit at date `n`.

Choose player `1`'s relevant rewards as

\[
 r_1(\{1\})=0,\qquad r_1(\{2\})=0,\qquad
 r_1(\{1,2\})=1,
\tag{7.1}
\]

and take every other relevant reward coordinate to be zero.

Then:

1. under the source response, absorption at date `n` is the singleton
   `{1}` and player `1` receives zero;
2. under the endpoint response, absorption at date `n` is the pair `{1,2}`
   and player `1` receives one;
3. the response-square terminal contribution is exactly one;
4. at the endpoint-response profile, player `1`'s payoff and unrestricted
   cap are both one, so its endpoint debt is exactly zero; but
5. in the literal source and mover-reset endpoint profiles, player `1` quits
   surely at date zero, so actual reach to date `n` is exactly zero.

The deleted-`1` law sees the unit car at date `n`; the actual law sees only
date zero.  No coupling, disintegration, common subsequence, or compact time
change can turn the counterfactual car into an actually reached one.  A
producer that needs a literal post-mark port must add an owner-survival/actual
reach hypothesis, or obtain it from new strategic mathematics.  The static
vanishing-debt atom alternative does not contain it.

This regression is local rather than a positive-minimum counterexample.  The
literal source has zero debt, while the mover-reset endpoint has player `1`
debt one and the endpoint-response profile has player `1` debt zero.  Thus it
models exactly a unit endpoint debt rise followed by the zero-debt common
response, but it does not realize a globally positive minimum.  Its role is
to refute the proposed **logical adapter from the atom/debt fields to actual
reach**; it does not assert existence of a positive-minimum quitting game.

## 8. Checked declarations and files inspected

The ordinary proof above uses the semantics exposed by the following checked
declarations.

- `quittingRootSequencePureTimeTerminalValue_some_eq` and
  `tendsto_quittingLiveLedgerAccum`, in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`;
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` and
  `quittingTerminalPayoff_update_pureTimeBehaviorStrategy`, in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `quittingRootSequencePureTimeTerminalValue` and the fixed-opponent Bellman
  identities, in
  `UniformEquilibrium/Quitting/Cycles/InfinitePureTimeExtremality.lean`;
- `abs_quittingFixedOpponentsContinueReward_le`, in
  `UniformEquilibrium/Quitting/Classification/Existence/PureTimeDeviationLedger.lean`;
- the fixed-opponent Quit-versus-solo bound used in (2.3), exposed as
  `abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass`
  and its unit-solo specialization
  `abs_quittingFixedOpponentsQuitValue_sub_one_le`;
- `HasQuittingStoppingLawVanishingDebtAtomAlternative` and
  `QuittingStoppingLawCommonResponseWitness`, in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/VanishingDebtAtomAlternative.lean`;
- `QuittingPositiveMinimumDebtTangentFamily.nonempty_vanishingDebtAtomAccess`,
  in
  `UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean`.

I also checked the current scope statements in `docs/TOOLKIT.md` and
`docs/FRONTIER.md`, especially the entries for the finite-quitting
uniform-existence boundary, generated-secant chronological debt, and
chronological marked-law absorption paths.  The existing chronological
marked-law path is an actual-law construction.  I found no named declaration
that packages the finite-family, all-cap response trace of Theorem 4.1.

## 9. Next exact question

Can the positive-minimum strategic source force, in the response-square arm,
either

\[
 \Pr(\text{observer survives on-path to the selected cap interval})\ge r>0
\]

or a second actual-law contribution on the same common-clock interval?
Section 7 proves that this cannot follow from the static atom and zero-debt
fields alone.  Such a theorem would be the minimal bridge from the typed
compact trace to an executable Tier-I port.
