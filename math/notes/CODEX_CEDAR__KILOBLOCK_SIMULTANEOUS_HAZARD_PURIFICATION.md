# CODEX_CEDAR — simultaneous-hazard purification of the Q-side kiloblock

## Current best attempt

**Exact reviewable result.**  Proposition 9 constructs a literal scaled
paired-singleton standard-Q/no-homogeneous `BuildingBlock` with active
singleton masses `1/6,1/6` and advance mass `2/3`.  Proposition 10 proves
that no sequence of finite ordinary independent-clock blocks can preserve
those payoffs and that advance mass, make collisions vanish, and make both
active owners' pure-Continue deviations asymptotically unprofitable.  Its
quantitative limit is `liminf eta>=1/72`.  Propositions 1--1B remain the
positive prescribed-law compiler that this strategic obstruction defeats.

**Conjecture-closing thesis tested here.**  The proposed thesis was to apply a
time-inhomogeneous simultaneous-hazard compiler blockwise to the finite
`KiloblockConstruction` behind the standard-Q/no-homogeneous public-signal
branch.  Proposition 10 refutes that thesis at the literal source-block
level: prescribed first-hit purification does not preserve the owner-deleted
laws.  A later-block signed compensation mechanism would be a different
producer and is not claimed here.

**Honest status and main gap.**  Propositions 1--10 are proved in ordinary
mathematics.  Proposition 1 compiles the prescribed first-hit law, and
Proposition 3 shows that the old pairwise-precedence obstruction is only
`O(epsilon)` on an actual multi-restart packet.  Proposition 4 is a sharp
negative test: even an exact public two-owner packet with the right prescribed
payoff can have a fixed ordinary exploitability gap because deleting one
owner exposes a different clock law.  Proposition 5 gives the exact pure-Never
gain for every proportional simultaneous-rate macro.  Propositions 6--7 give
sharp leakage bounds for distinct and common latent blocker clocks.  No
all-deleted-clock purifier is proved.  Proposition 8 turns the common-blocker
law into an exact `1/6` refusal threshold for a three-clock payoff packet.
Proposition 9 gives a literal scaled paired-singleton
standard-Q/no-homogeneous `BuildingBlock` whose two active singleton masses
are exactly `1/6`; its remaining `2/3` mass advances.  Thus the threshold is
sharp on actual source data.  Proposition 10 shows that ordinary blockers
cannot be both chronologically abundant and prescribed-invisible at joint
survival `2/3`, and restores a fixed two-owner refusal gap.  The notebook is
therefore **closed as a universal blockwise compiler**.  The earlier
description of the gap as merely a survival barycenter was too weak and is
corrected in Sections 7--9.

Propositions 9--10 were independently falsification-audited and accepted as
valid ordinary mathematics in
`feedback/CODEX_CEDAR__KILOBLOCK_SIMULTANEOUS_HAZARD_PURIFICATION__BY_CODEX_GAUSS.md`.
That review also confirms the local-only scope: no full counterexample is
inferred.

**Sections to check.**  Sections 2 (source/interface status), 3 (exact macro
law), 7 (semantic correction), 8 (actual restart-packet estimate), 9
(two-owner deleted-clock falsifier), 10 (latent-clock leakage), and 11
(the exact paired source block), and 12 (the quantitative local no-go).

**Kill criterion (met).**  Abandon this route if one actual
standard-Q/no-homogeneous, negative-margin source block admits a fixed positive
ordinary terminal exploitability gap for every time-inhomogeneous product
clock path whose prescribed and all player-deleted laws stay in the source
carrier.  Propositions 9--10 supply exactly the source-matched block and its
fixed blockwise gap.  This closes the compiler architecture, not the full
quitting-game conjecture and not a distinct later-block compensation route.

## 1. Scope

This is ordinary mathematics, not checked in Lean.  The route is distinct
from:

- Simon `F_epsilon`/orbit necessity;
- finite-depth punishment-floor admissible return chains; and
- the closed one-active deterministic schedule in
  `CODEX_CEDAR__PREDICTABLE_SINGLE_OWNER_DERANDOMIZATION.md` and
  `CODEX_CEDAR__PROJECTIVE_Q_DETERMINISTIC_KILOBLOCK.md`.

The desired endpoint is an ordinary quitting profile against every
behavioral unilateral deviation.  The public-signal construction is source
data, not itself an ordinary-game strategy.

## 2. Exact source and declaration ledger

The bounded lookup inspected the following named material.

- `faithful_q_nonQ_lcp_matrix_gate`, `StandardQMatrixSide`, and
  `ResidualHardClass` in
  `UniformEquilibrium/Quitting/Classification/LCP/Gate.lean`.
- `exists_uniformEquilibriumPayoff_or_standardQMatrixSide` in
  `UniformEquilibrium/Quitting/Classification/LCP/StationaryExistence.lean`.
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`.
- `collisionMass_logarithmicBlock_le_sq` in
  `UniformEquilibrium/Quitting/AbsorptionPath/LogarithmicBlockDiscretization.lean`.
- `scale_eq_one_of_conditionedProductPurification_two_active` and
  `no_conditionedProductPurification_of_two_active_phantom` in
  `UniformEquilibrium/Quitting/Cycles/ConditionedProductPurification.lean`.
  These forbid a particular *exact* rowwise conditioned purification; they do
  not forbid the asymptotic macro law below.
- Paper-facing `BuildingBlock`, `BuildingAttempt`,
  `KiloblockConstruction`, `KiloblockConstruction.exitMass_mul_w`,
  `KiloblockConstruction.macro_balance`,
  `exists_kiloblockConstruction`, and `theorem2_13_sunspot` in
  `Literature/SolanAndSolan2020.lean`.

The `Literature/` file is non-built and contains paper claims with `sorry`.
It is a mathematical source, not a production `L`, `A`, or `C` seal.  A full
positive result must either prove the needed matrix-to-block facts in ordinary
mathematics or use exact checked replacements; it may not cite the paper
statement as an integrated producer.

The old one-active route is genuinely unavailable: the checked
`periodTwo_residualHardClass` table has an audited positive exploitability
floor for every ordinary one-active profile, while its exact ordinary
equilibrium uses two active hazards.  This motivates simultaneous rather than
calendar-selected owners.

## 3. Exact simultaneous-hazard macro law

Let `J` be a finite label set.  Fix desired public macro masses

\[
 a_i\ge0,\qquad A=\sum_i a_i<1,
 \qquad s=1-A>0.
\]

The label `i` means that the macro absorbs at singleton `{i}`; `s` is the
total mass that survives to a continuation.  If `A=0`, use all Continue, so
assume `A>0`.  Put

\[
 \Lambda=-\log s>0,qquad
 \lambda_i=\Lambda a_i/A.
\]

For integer `N>=1`, repeat one product row `N` times, with player `i`'s
per-row Quit probability

\[
 p_{i,N}=1-e^{-\lambda_i/N}.
\]

Let `q_N` be its one-row all-Continue probability.

### Proposition 1 (proved, ordinary mathematics)

The macro has:

1. exact survival `q_N^N=s`;
2. singleton-`i` absorption mass

   \[
   A_{i,N}=(1-s)\,
   \frac{e^{-(\Lambda-\lambda_i)/N}
          (1-e^{-\lambda_i/N})}
        {1-e^{-\Lambda/N}},
   \]

   with `A_{i,N}->a_i`; and
3. total collision mass

   \[
   C_N=1-s-\sum_i A_{i,N}\to0.
   \]

For fixed finite data, `C_N=O(1/N)`.

### Proof

Independence gives

\[
 q_N=\prod_i e^{-\lambda_i/N}=e^{-\Lambda/N},
\]

so `q_N^N=e^{-Lambda}=s`.  In one row, exact singleton `i` has probability

\[
 e^{-(\Lambda-\lambda_i)/N}(1-e^{-\lambda_i/N}).
\]

Multiply this by the geometric reach sum
`sum_{t=0}^{N-1}q_N^t=(1-s)/(1-e^{-Lambda/N})` to obtain the displayed
formula.  The ratio tends `lambda_i/Lambda=a_i/A`; since `1-s=A`, its limit
is `a_i`.

The terminal alternatives before the continuation are disjoint singleton
and multi-quitter coalitions, hence their masses sum to `1-s`.  This gives
the formula for `C_N` and its convergence.  A second-order expansion of the
finite product gives the `O(1/N)` bound; equivalently, sum the per-row
pair-collision bound against the geometric reach weights.  No exact
conditioned-product identity is asserted.

### Proposition 1B (proved: zero-survival boundary)

If `sum_i a_i=1`, the same conclusion holds asymptotically with survival
tending to zero.  Choose any `Lambda_N -> infinity` with
`Lambda_N^2/N -> 0` (for example `Lambda_N=N^(1/3)`) and repeat `N` rows with

\[
 p_{i,N}=1-\exp(-\Lambda_N a_i/N).
\]

Then macro survival is `exp(-Lambda_N)->0`, singleton-`i` mass tends to
`a_i`, and collision mass tends to zero.  Indeed, with
`x_N=Lambda_N/N->0`, the exact singleton formula is

\[
 (1-e^{-\Lambda_N})
 e^{-(1-a_i)x_N}\frac{1-e^{-a_ix_N}}{1-e^{-x_N}},
\]

whose limit is `a_i`.  The summed pair-collision error is
`O(Lambda_N^2/N)`.  This boundary case is needed when
`KiloblockConstruction.macroAdvanceProbability` is zero; the positive
`exitMass` theorem still ensures nonzero singleton absorption.

## 4. Payoff approximation with one deterministic continuation

Let `r^i` be the payoff vector at singleton `{i}` and let `y` be the terminal
payoff vector of one deterministic ordinary continuation entered after the
macro survives.  Let `M` bound every terminal reward and every coordinate of
`y`.  The ordinary macro payoff is

\[
 U_N=\sum_i A_{i,N}r^i+s y+E_N,
\]

where the collision contribution satisfies

\[
 \|E_N\|_\infty\le M C_N.
\]

### Proposition 2 (proved, ordinary mathematics)

For the target macro payoff

\[
 U=\sum_i a_i r^i+s y,
\]

one has

\[
 \|U_N-U\|_\infty
 \le M\left(C_N+\sum_i|A_{i,N}-a_i|\right)\to0.
\]

The same coupling bounds any unilateral behavioral deviation whose two
compared macros use the same deterministic continuation, with the relevant
player-deleted reach replacing joint reach.  This does **not** yet compare an
ordinary continuation with the public mixture of continuations.

## 5. The exact survival-continuation seam

A public macro does not merely specify absorbing masses.  Conditional on the
event of no quit, the observed label may select a continuation payoff `y^k`.
Write its survival masses as `s_k`, so that `sum_k s_k=s`.  Its expected
macro payoff is

\[
 U^{pub}=\sum_i a_i r^i+\sum_k s_k y^k.
\]

At the level of prescribed payoff alone, Proposition 2 matches this by
choosing the barycenter

\[
 \bar y=s^{-1}\sum_k s_k y^k.
\]

But `bar y` is only a vector.  Ordinary quitting play has no nonabsorbing
public event that selects `k`, and independent private mixing does not make a
common continuation state.  A valid compiler therefore needs a profile
whose reached continuation payoff and every player's continuation best-reply
cap jointly approximate the corresponding barycenter.  Convexity of payoff
vectors alone is not enough.

For a source `BuildingBlock`, each attempt continuation is either `restart`
at `w` or `advance` to `y`.  Thus the public survival barycenter lies on the
segment `[w,y]`, but neither endpoint nor an arbitrary segment point is known
to be an ordinary realized semantic pair with the required caps.  The public
balance equation proves unconditional harmonicity; it does not supply this
semantic convexification.

This identifies the exact new universal obligation:

> Construct a deterministic causal path through the source carrier whose
> reached semantic pairs realize the public restart/advance survival
> barycenters up to summable error, while simultaneous product rows realize
> the absorbing label masses and keep every active/local deviation inequality.

Unlike the closed one-active schedule, the ordinary row at a macro stage may
give several players positive hazards.  Collision terms are explicitly paid
by Proposition 1 rather than assumed absent.

## 6. Proved versus unproved

### Proved here

- Proposition 1: exact survival and asymptotically exact singleton absorption
  law for simultaneous product macros, with vanishing collisions.
- Proposition 1B: the source-relevant zero-advance boundary via slowly
  diverging total intensity.
- Proposition 2: the corresponding bounded prescribed-payoff approximation
  for one deterministic continuation.
- Sections 7--9 sharpen the remaining public-signal content to every
  player-deleted clock law and its reached continuation semantic pair.

### Not proved

- A time-inhomogeneous continuation path with all prescribed and
  player-deleted best-reply caps.
- Local Nash transport for the full restart/advance kiloblock controller.
- An actual checked matrix-to-block producer in the production lane.
- The all-errors ordinary profile and fixed target.

## 7. Correction: restart collapse is not semantic collapse

The first formulation in Section 5 isolated the conditional survival
barycenter.  Summing the public restart loop shows that this is not quite the
sharp obstruction.  At the level of prescribed terminal lotteries, one block
has the exact collapsed identity

\[
 w=a y+\sum_i\theta_i M_{\cdot i},
 \qquad a+\sum_i\theta_i=1.
\]

Thus one may send every surviving prescribed path to `y`; no vector-valued
barycenter is needed.  This collapse is still not valid for deviations.  A
restart label sends an owner who Continues back to `w`, whereas the collapsed
ordinary macro sends that owner toward `y`.  Deleting the owner's clock can
therefore change the probability of reaching the terminal continuation by an
order-one amount even when the prescribed first-hit laws agree exactly.

The correct object to purify is consequently the tuple

```text
(prescribed first-hit law,
 every owner-deleted first-hit law,
 reached continuation semantic pair under each deletion).
```

Propositions 1--2 construct only the first component.  This is also why a
fixed vector of simultaneous rates can fail.  In the collisionless continuous
limit, if rates `lambda_i` are used until a fixed terminal time and the tail
is `y`, the conditional prescribed value is

\[
 V(t)=\int_t^T e^{-L(u-t)}M\lambda\,du
       +e^{-L(T-t)}y,
 \qquad L=\sum_i\lambda_i.
\]

An owner with positive rate on an interval can delete its clock on that
interval.  Exact support indifference would require `V_i(t)=0` there; if the
same support persists, differentiation forces

\[
 (M\lambda)_i=0
 \quad\text{on every active coordinate.}             \tag{7.1}
\]

Hence an identical-rate macro is not a strategic compiler on a generic
no-homogeneous block.  A viable construction must vary its active support and
retain the counterfactual late clocks exposed by every deletion.

## 8. The actual multi-restart packet defeats the coarse precedence no-go

There is nevertheless a source-specific positive estimate.  Fix one literal
`BuildingBlock M y epsilon` with the negative-column attempts.  Let `R` be
the positive-public-mass restart owners and `A` the positive-public-mass
advance owners.  Write

\[
 \beta_i=z_iq_i\quad(i\in R),\qquad
 B=\sum_{i\in R}\beta_i,
 \qquad d=z_0+\sum_{i\in A}z_i.
\]

After collecting the nonrestart choices into their normalized mean `U`, the
balance equation is

\[
 (1-\rho)w=M\beta+dU,
 \qquad \rho=\sum_{i\in R}z_i(1-q_i).                \tag{8.1}
\]

On the actual no-homogeneous source branch, `d>0`: if `d=0`, normalizing
`beta` in (8.1) gives a nontrivial homogeneous projective-LCP solution.  The
lower field gives `U_k>=-epsilon` for every coordinate.

### Proposition 3 (proved, ordinary mathematics)

For every `i in R`,

\[
 w_i=0,
 \qquad
 -\epsilon\sum_{j\in R}z_j
 \le (M\beta)_i=-dU_i\le d\epsilon.                 \tag{8.2}
\]

In particular `|(M beta)_i|<=epsilon`.  Moreover, define the pairwise
precedence interval for the unnormalized restart masses by

\[
 L_R=\sum_{i<j}\beta_i\beta_j\min(M_{ij},M_{ji}),
 \qquad
 U_R=\sum_{i<j}\beta_i\beta_j\max(M_{ij},M_{ji}).   \tag{8.3}
\]

Then

\[
 \operatorname{dist}(0,[L_R,U_R])\le\epsilon B.     \tag{8.4}
\]

Thus the mesh-independent pairwise obstruction in Proposition 9.1 of
`CODEX_CEDAR__PROJECTIVE_Q_DETERMINISTIC_KILOBLOCK.md` cannot remain separated
from zero at the source accuracy scale on the actual restart packet.  This is
only a necessary aggregate test, not an all-suffix schedule.

### Proof

For `i in R`, complementarity and `q_i<1` give `w_i=0`.  For `j in R`, the
attempt identity therefore reads

\[
 w^j_i=q_jM_{ij}\ge-\epsilon.
\]

Multiplying by `z_j` and summing proves the lower bound in (8.2).  Coordinate
`i` of (8.1), followed by `U_i>=-epsilon`, proves the equality and upper
bound.

Put

\[
 Q=\sum_i\beta_i(M\beta)_i
   =\sum_{i<j}\beta_i\beta_j(M_{ij}+M_{ji}).
\]

Equation (8.2) gives `Q<=d epsilon B`, and therefore
`L_R<=Q/2<=epsilon B/2`.  On the other side,

\[
 \max(M_{ij},M_{ji})
 \ge -\frac{\epsilon}{\max(q_i,q_j)}.
\]

Consequently

\[
 U_R\ge-\epsilon\sum_{i<j}z_iz_j\min(q_i,q_j)
     \ge-\epsilon B,
\]

because

\[
 \sum_{i<j}z_iz_j\min(q_i,q_j)
 \le\sum_i z_iq_i\sum_{j\ne i}z_j\le B.
\]

If the interval lies above zero, its lower endpoint is at most
`epsilon B/2`; if it lies below zero, its upper endpoint is at least
`-epsilon B`.  This proves (8.4).

The calculation matters because it uses the *actual* lower field and restart
orientation.  An abstract complementary packet does not have (8.2).

## 9. Exact deleted-clock falsifier for the bare public packet

The preceding estimate does not control a player-deleted survival law.  The
smallest exact example shows that no theorem based only on prescribed
singleton masses can do so.

Consider the two-player terminal table

```text
r({1})=(0,1),  r({2})=(1,0),
r({1,2})=(0,0),  r(empty)=(0,0).
```

A public signal chooses owner `1` or `2` with probability `1/2`.  The chosen
owner Quits with total probability `gamma in (0,1)` and otherwise both
players Never quit.  This is an exact public-signal Nash profile: the chosen
owner always receives zero, while the other owner cannot improve on its
positive chance of receiving one.  Its payoff is

\[
 (\gamma/2,\gamma/2).                                \tag{9.1}
\]

### Proposition 4 (proved, ordinary mathematics)

For every ordinary behavioral profile in this two-player game, let `u_i` be
its prescribed payoff and let `g_i` be player `i`'s gain from changing to
pure Never.  Then

\[
 g_1+g_2\ge u_1u_2.                                 \tag{9.2}
\]

Hence an ordinary terminal `eta`-Nash profile satisfies
`u_1u_2<=2 eta`.  In particular, if both coordinates are within `gamma/4` of
the public payoff (9.1), then

\[
 \eta\ge\gamma^2/32.                                \tag{9.3}
\]

### Proof

Before absorption, the only observed history is the deterministic string of
all-Continue outcomes.  The two players' private behavioral randomizations
therefore induce independent planned quit times
`T_1,T_2 in Nat union {Never}`.  Put

\[
 a=\Pr(T_1<\infty),\qquad b=\Pr(T_2<\infty).
\]

Then

\[
 u_1=\Pr(T_2<T_1),\qquad u_2=\Pr(T_1<T_2),
\]

while deletion gives

\[
 g_1=\Pr(T_1\le T_2<\infty),\qquad
 g_2=\Pr(T_2\le T_1<\infty).
\]

On the event that both times are finite, at least one of the two weak orders
holds.  Independence therefore gives `g_1+g_2>=ab`.  Also `u_1<=b` and
`u_2<=a`, proving (9.2).  The Nash and neighborhood claims follow
immediately.

This packet can be embedded in the bare `BuildingBlock` fields.  On three
coordinates take columns

\[
 M_{\cdot1}=(0,1,0),\quad
 M_{\cdot2}=(1,0,0),\quad
 M_{\cdot3}=(-1,-1,0),
\]

take `y=0`, `epsilon=gamma`, attempts
`w^i=gamma M_{.i}`, and public weights `z_1=z_2=1/2`, `z_3=z_0=0`.
Then `w=(gamma/2,gamma/2,0)`, both `y` and `w` lie in `D_0`, all lower and
complementarity fields hold, and every approach is nontrivial.  The first two
columns, however, have no negative coordinate, and the matrix is not the
actual standard-Q/no-homogeneous negative-margin source.  Proposition 4
therefore falsifies a bare-`BuildingBlock` purifier but does not meet the kill
criterion at the top of this notebook.

### Proposition 5 (proved: exact refusal gain for proportional rates)

Fix a collisionless continuous race on a bounded time interval.  Let total
survival be `s in (0,1)`, and suppose player `j` has a constant share `mu_j`
of the total hazard after an arbitrary deterministic time change.  Put

\[
 m_i=\sum_j\mu_jM_{ij}.
\]

Assume `M_ii=0`, `0<mu_i<1`, the terminal continuation pays `y_i>=0`, and
the prescribed coordinate is pinned at zero:

\[
 (1-s)m_i+s y_i=0.                                  \tag{9.4}
\]

If player `i` deletes its clock, its payoff is

\[
 n_i=y_i\left[
 s^{1-\mu_i}
 -\frac{s(1-s^{1-\mu_i})}{(1-s)(1-\mu_i)}
 \right]\ge0.                                       \tag{9.5}
\]

The inequality is strict when `y_i>0`.  Thus no proportional-rate
simultaneous macro can support an active owner with a strictly positive tail,
even when its prescribed start coordinate is exactly pinned.  A valid path
must change hazard proportions over time or use nonvanishing collision rows.

### Proof

Write `k=1-mu_i`.  Deleting `i` changes total survival from `s` to `s^k`
and changes the conditional singleton mixture from `m_i` to `m_i/k`.
Therefore

\[
 n_i=(1-s^k)m_i/k+s^k y_i.
\]

Substituting `m_i=-s y_i/(1-s)` from (9.4) gives (9.5).  Convexity of
`x |-> s^{-x}` on `[0,1]` gives the chord bound

\[
 s^{-k}-1\le k(s^{-1}-1).
\]

After multiplication by `s`, this is exactly

\[
 s(1-s^k)\le s^k k(1-s),
\]

so the bracket in (9.5) is nonnegative.  Strict convexity makes it strict for
`0<k<1`; multiplying by `y_i>0` proves the final claim.

## 10. Two latent outside clocks inherit the pair-leakage obstruction

The standard-Q escape vector is not yet a chronology.  This can be seen
without rewards.  Let `T_i,T_k,T_o,T_h` be four independent planned quit
times, with values in `Nat union {Never}`.  Think of `o` as a blocker that is
supposed to be invisible while `i` follows its clock but exposed after `i`
deletes that clock; define `h` symmetrically for `k`.  Put

\[
 A=\{T_i\le T_o<\min(T_k,T_h)\},
 \qquad
 B=\{T_k\le T_h<\min(T_i,T_o)\},                    \tag{10.1}
\]

and write `a=P(A)`, `b=P(B)`, `ell=1-a-b`.

### Proposition 6 (proved, ordinary mathematics)

One has

\[
 \sqrt a+\sqrt b\le1,
 \qquad \ell^2\ge4ab.                               \tag{10.2}
\]

### Proof

Event `A` implies both `T_i<T_k` and `T_o<T_h`; these two strict-order
events depend on disjoint pairs of independent clocks.  With

\[
 x=\Pr(T_i<T_k),\qquad y=\Pr(T_o<T_h),
\]

we get `a<=xy`.  Event `B` implies the reverse two strict orders, whose
probabilities are at most `1-x` and `1-y`, including all ties and Never atoms
in the complements.  Thus `b<=(1-x)(1-y)`.  Cauchy--Schwarz gives

\[
 \sqrt a+\sqrt b
 \le\sqrt{xy}+\sqrt{(1-x)(1-y)}\le1.
\]

The leakage bound follows by squaring
`ell=1-a-b >= 2 sqrt(ab)`.

This is the already reviewed independent-clock pair inequality applied to
the *nested deletion-exposure events* rather than to two simultaneous target
pairs.  It adds no novelty claim to that clock law.  Its source-facing force
is different: merely adding two zero-prescribed-mass outside LCP owners cannot
make both deleted laws strongly absorbing without paying a prescribed
chronology leakage account.

The same obstruction survives when one blocker is asked to serve both
owners; this requires a different proof.

### Proposition 7 (proved: common middle-clock inequality)

Let `X,Y,Z` be independent clocks in `Nat union {Never}` and put

\[
 a=\Pr(X<Z<Y),\qquad b=\Pr(Y<Z<X),
 \qquad \ell=1-a-b.
\]

Then again

\[
 \ell^2\ge4ab.                                      \tag{10.3}
\]

### Proof

Set `U=1_{X<Z}` and `V=1_{Y<Z}`.  Conditional on `Z=z`, the Bernoulli
variables `U,V` are independent, with parameters

\[
 f(z)=\Pr(X<z),\qquad g(z)=\Pr(Y<z).
\]

Both `f` and `g` are nondecreasing on the totally ordered clock space.  For
an independent copy `Z'`,

\[
 2\operatorname{Cov}(f(Z),g(Z))
 =\mathbb E[(f(Z)-f(Z'))(g(Z)-g(Z'))]\ge0.
\]

Thus `U,V` are positively associated.  If
`p_uv=Pr(U=u,V=v)`, the two-by-two determinant form is

\[
 p_{00}p_{11}\ge p_{10}p_{01}.                     \tag{10.4}
\]

The strict middle events satisfy `a<=p_10` and `b<=p_01`; the differences
are precisely tie/boundary cases already assigned to leakage.  Therefore

\[
 \ell\ge p_{00}+p_{11}
 \ge2\sqrt{p_{00}p_{11}}
 \ge2\sqrt{p_{10}p_{01}}
 \ge2\sqrt{ab}.
\]

Squaring proves (10.3).  The proof includes arbitrary atoms and Never mass;
no density or finite-horizon assumption is used.

### Proposition 8 (proved: a three-clock refusal threshold)

Consider a three-player terminal table with reward bound `M>=3`.  In the
coordinates of owners `X,Y`, assume the singleton rewards are

```text
                 own X/Y     other main owner     blocker Z
coordinate X        0                3                -1
coordinate Y        0                3                -1.
```

All other terminal rewards are arbitrary in `[-M,M]`.  For an ordinary
behavioral profile, define the four strict order masses

\[
 a=\Pr(X<Z<Y),\quad b=\Pr(Y<Z<X),
 \quad c=\Pr(X<Y<Z),\quad d=\Pr(Y<X<Z),
\]

and put

\[
 f=1-a-b-c-d.
\]

Thus `f` contains every outcome where `Z` is first, every tie, and every
Never boundary.  Let the fully strictly ordered portions of the singleton
masses of `X,Y` be `s_X=a+c` and `s_Y=b+d`.  If the profile is terminal
`eta`-Nash and
`s_X,s_Y>=alpha`, then, with

\[
 \delta=\eta+2Mf,
\]

one necessarily has

\[
 6\alpha\le1+3f+4\delta.                            \tag{10.5}
\]

In particular, no sequence with `eta->0`, `f->0`, and
`liminf min(s_X,s_Y)>1/6` exists.

### Proof

When `X` changes to pure Never, the strict event `X<Y<Z` changes its payoff
from own singleton value zero to the other-owner value `3`; the event
`X<Z<Y` changes it from zero to blocker value `-1`.  On every event counted
by `b` or `d`, deleting `X` leaves the first quitter unchanged.  All remaining
changes occur inside the `f` account and have magnitude at most `2M`.
Therefore the Never gain satisfies

\[
 g_X\ge3c-a-2Mf.
\]

The Nash inequality `g_X<=eta` gives `a>=3c-delta`; symmetrically
`b>=3d-delta`.  Since `s_X=a+c` and `s_Y=b+d`,

\[
 a,b\ge(3\alpha-\delta)/4.                           \tag{10.6}
\]

Also

\[
 a+b\ge3(c+d)-2\delta.
\]

For `ell=1-a-b=c+d+f`, this rearranges to

\[
 4\ell\le1+3f+2\delta.                              \tag{10.7}
\]

Proposition 7 gives `ell^2>=4ab`; using (10.6), when its right side is
positive,

\[
 \ell\ge(3\alpha-\delta)/2.                         \tag{10.8}
\]

Combining (10.7)--(10.8) yields (10.5).  If
`3alpha<=delta`, inequality (10.5) is automatic, so the same conclusion
holds without a side condition.

This proposition is an unrestricted-behavior calculation: planned clocks
encode the whole on-path behavioral laws, and the selected deviation is pure
Never.  It is not a counterexample table.  Pure singleton profiles and the
`f` account may still supply ordinary equilibria.  Its use is as a source
filter: a rare-collision purifier of a public packet with two main singleton
masses above `1/6` must retain a nonvanishing blocker-first/tie/Never account.

## 11. An exact paired standard-Q block sits at the `1/6` boundary

The preceding inequality must now be tested against literal source geometry.
Let `P` be `pairedSingletonMatrix` from
`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingleton.lean`
and put `M=P/3`.  Its columns are

\[
 c_0=(0,1,-1/3,-1/3),\quad
 c_1=(1,0,-1/3,-1/3),
\]

\[
 c_2=(-1/3,-1/3,0,1),\quad
 c_3=(-1/3,-1/3,1,0).
\]

Fix `0<epsilon<1/3` and define

\[
 y=(0,0,1/6,1/6),\qquad w=(1/6,1/6,0,0).
\]

Let the public weights be `z_0=z_1=1/2`, `z_2=z_3=0`, with cemetery
weight zero.  For the two positive-weight owners take advance attempts of
quit weight `1/3`:

\[
 w^0=(2/3)y+(1/3)c_0=(0,1/3,0,0),
\]

\[
 w^1=(2/3)y+(1/3)c_1=(1/3,0,0,0).
\]

For the zero-weight owners choose

\[
 0<h:=\min(1/2,3\epsilon/2)<1,
 \qquad w^j=(1-h)y+hc_j\quad(j=2,3).               \tag{11.1}
\]

### Proposition 9 (proved: literal source block and sharpness)

The displayed data form a `BuildingBlock M y epsilon`.  The associated
attempts are all advance attempts.  Its collapsed macro has singleton
absorption masses

\[
 a_0=a_1=1/6,qquad a_2=a_3=0,
\]

and advance mass `2/3`.  Moreover `M` is standard Q, has no homogeneous
simplex-LCP solution, and every column has a distinct negative coordinate.
The standard-Q and no-homogeneous assertions here use elementary positive
scaling from the checked unscaled declarations
`pairedSingletonMatrix_standardQ` and
`pairedSingletonMatrix_noHomogeneous` in
`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonLCP.lean`;
the scaled adapter itself is ordinary mathematics, not a separately named
Lean declaration.

Consequently Proposition 8 is sharp at its limiting `1/6` mass on a literal
standard-Q/no-homogeneous negative-column source block.  It does not rule out
this block: after multiplying its owner coordinates by three, the two cross
rewards and a common blocker column have exactly the `0,3,-1` pattern, but
the macro retains the order-one advance account `2/3`.  Any universal clock
compiler must transport that advance tail and its player-deleted semantics;
it cannot prove that the leakage account vanishes.

### Proof

Both boundary points are explicitly in the nonnegative column hull:

\[
 y={1\over5}c_0+{1\over5}c_1+{3\over10}c_2+{3\over10}c_3,
\]

\[
 w={3\over10}c_0+{3\over10}c_1+{1\over5}c_2+{1\over5}c_3.
\]

Each has zero coordinates, so both lie in `DZero M`.  Every `w^j` is a
strict point of the segment from `y` to column `c_j`.  The only negative
coordinates among the attempts are `-h/3` in `w^2,w^3`; (11.1) gives
`-h/3>=-epsilon`.  The balance and complementarity fields are literal:

\[
 {1\over2}w^0+{1\over2}w^1=w,qquad
 (w^0)_0=(w^1)_1=0.
\]

The positive public mass is one.  This verifies every `BuildingBlock`
field.  Each positive-weight attempt quits with weight `1/3`; because it is
an advance attempt, its nonquit weight `2/3` exits the block rather than
restarting.  Multiplication of a matrix by a positive scalar preserves
standard-Q solvability (scale the right-hand side) and preserves the
homogeneous complementarity equations.  The checked properties of `P`
therefore pass to `M=P/3`.  Its displayed columns give the negative witnesses.

## 12. The paired macro has a fixed blockwise ordinary refusal gap

Proposition 9's order-one advance mass does not by itself repair the two-owner
refusal gap.  The following statement allows arbitrary time-inhomogeneous
product rows and both negative blockers.

Fix a finite block.  Before absorption its public history is only the string
of all-Continue outcomes, so an arbitrary ordinary behavioral profile induces
four independent planned clocks

\[
 T_j\in\{0,\ldots,H-1,\infty\}.
\]

At a unique finite minimum `j`, pay column `c_j` of Proposition 9.  At a tie
of two or more finite minima, allow an arbitrary reward in `[-1,1]^4`.  If all
four clocks are infinite, continue to a semantic tail whose first two payoff
coordinates are `y_0=y_1=0`.  Write:

- `S_j` for the probability that `j` is the unique first clock;
- `C` for total tie/collision probability;
- `s` for joint block survival;
- `u_i` for prescribed payoff, `i=0,1`;
- `n_i` for the payoff when `i` uses pure Continue throughout this block and
  then resumes the same tail behavior; and
- `eta` for a bound `n_i-u_i<=eta`, `i=0,1`.

Put

\[
 \tau=\max(|u_0-1/6|,|u_1-1/6|),\qquad
 \sigma=|s-2/3|,
\]

\[
 B=S_2+S_3,qquad
 \kappa=\Pr(T_2<\infty\ \hbox{or}\ T_3<\infty).
\]

### Proposition 10 (proved: quantitative blockwise no-go)

The blocker and blocker-clock masses obey

\[
 B\le {3\over5}(\sigma+2\tau+C),                  \tag{12.1}
\]

and, whenever `s>0`,

\[
 \kappa\le {B+C\over s+B+C}.                      \tag{12.2}
\]

If

\[
 L:=1/6-\tau-2(\kappa+C)>0,
\]

then

\[
 2\eta\ge L^2-8(\kappa+C).                        \tag{12.3}
\]

In particular, there is no sequence of such ordinary blocks for which

\[
 (u_0,u_1)\to(1/6,1/6),\quad s\to2/3,\quad
 C\to0,\quad\eta\to0.                             \tag{12.4}
\]

Indeed (12.1)--(12.2) force `kappa->0`, while (12.3) gives
`liminf eta>=1/72`.

This is an all-time-inhomogeneous, arbitrary-behavior *local block* no-go,
not a counterexample to the quitting-game conjecture.  A global chained
construction could in principle compensate a refusal gain at a different
reached block, and the concrete paired completion already has a checked pure
stationary equilibrium.  What fails is the proposed compiler that replaces
this literal public block by a locally Nash ordinary product block while
preserving its payoff, advance probability, and vanishing collision mass.

### Proof

For the first two coordinates, the singleton table and zero tail give

\[
 u_0=S_1-B/3+e_0,\qquad u_1=S_0-B/3+e_1,
 \qquad |e_i|\le C.                                \tag{12.5}
\]

Hence

\[
 S_0,S_1\ge1/6-\tau+B/3-C.
\]

Using `S_0+S_1+B+C+s=1` gives

\[
 1-s\ge1/3-2\tau+5B/3-C,
\]

which implies (12.1).

Let `r_j=Pr(T_j=infinity)` and `r_B=r_2r_3=1-kappa`.
On the event that both main clocks are infinite and at least one blocker
clock is finite, the realized terminal outcome is either a unique blocker or
a blocker collision.  Independence therefore gives

\[
 r_0r_1\kappa\le B+C.
\]

Since `s=r_0r_1(1-kappa)`, rearrangement proves (12.2).  This is the key
source-matched point: blockers cannot be chronologically abundant but
prescribed-invisible when the joint advance probability stays `2/3`.

For the final inequality, couple to the ideal two-player clock game from
Proposition 4 by forcing clocks `2,3` to infinity and paying zero at a
main-player tie.  Denote its prescribed payoffs and pure-Continue gains by
`u_i^*` and `g_i^*`.  The coupling changes a prescribed payoff only when a
blocker clock is finite or the original block collides, so

\[
 |u_i-u_i^*|\le2(\kappa+C).
\]

After player `i` is deleted, the coupling can differ only when a blocker
clock is finite, hence the gain comparison is safely bounded by

\[
 |(n_i-u_i)-g_i^*|\le4(\kappa+C).                 \tag{12.6}
\]

Proposition 4 gives

\[
 g_0^*+g_1^*\ge u_0^*u_1^*.
\]

Both ideal prescribed payoffs are probabilities and, by the first coupling
bound, are at least `L`.  Summing (12.6) and using the two assumed refusal
caps proves (12.3).

## 13. Revised universal obligation and next exact check

The route has narrowed to a source-specific clock theorem:

> From the negative-margin standard-Q building-block chain, construct one
> time-inhomogeneous product clock path such that the prescribed first-hit
> law and every owner-deleted first-hit law satisfy the public block caps,
> with summable collision and tracking error.

Proposition 3 says that the multi-restart packet passes the first aggregate
precedence test.  Propositions 4--6 say that an advance packet with a positive
cross-precedence cycle cannot be repaired by proportional simultaneous rates
or by two cheaply hidden outside clocks.  Standard-Q cross-face support escape
is already proved in ordinary mathematics in Proposition 44 of
`CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`; repeating that algebra is not a
new producer, and the result itself explicitly lacks a floor-admissible
return.

Propositions 9--10 answer the previous threshold check.  The source packet
sits exactly at `1/6`, its advance mass is order one, and no independent-clock
block with vanishing collisions can preserve those data while making the two
active owners locally Nash.  The original blockwise simultaneous-hazard
compiler is therefore **closed as a universal source-block compiler**.  This
does not settle the full route in which a later reached block deliberately
pays the current refusal premium.

Any surviving causal-chain thesis must therefore write the paired block's two
owner-deletion Bellman identities with a literal continuation semantic pair
at `y`, and make a later reached block pay both current refusal premiums on
the *same path*.  The exact next check is whether summing those premiums over
a returned finite chain telescopes to a positive boundary term, or whether a
signed continuation debt can cancel it without violating the punishment
floor.  A contradiction must survive arbitrary time-inhomogeneous product
clocks; a construction must match joint survival and each of the four
player-deleted survivals.  Other singleton events, ties, collisions, and
Never atoms remain explicit.  The LCP support-escape vector alone is not a
chronology.
