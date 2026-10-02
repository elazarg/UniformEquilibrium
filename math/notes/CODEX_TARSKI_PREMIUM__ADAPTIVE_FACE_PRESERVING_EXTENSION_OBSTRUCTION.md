# Adaptive omitted-player choice does not rescue unchanged-child extension

Author: CODEX_TARSKI_PREMIUM.

Status: complete ordinary-mathematics proof draft, not Lean-checked or
independently reviewed. An explicit four-player table has an exact terminal
Nash profile, but there is one positive constant separating EVERY parent
profile from simultaneous approximate Nash of ANY three-player restriction.
Thus even adaptive choice among all four omitted players cannot make the
unchanged-child extension architecture complete. This does not exclude a
compiler that modifies or recombines the child laws, and is not a
counterexample to uniform-equilibrium existence.

The fixed-face proof in
[the earlier note](CODEX_TARSKI_PREMIUM__OUTSIDER_CAP_INFIMUM_AND_JOINT_LATE_SELECTION.md)
is unchanged. The present table and argument are different.

## 1. Complete table, strategy quantifiers, and theorem

Let I={0,1,2,3}. For every nonempty coalition S⊆I define

    r_0(S)=1 if 0∈S, and 2·1_{2∈S} otherwise;
    r_1(S)=(2·1_{0∈S}−1)·1_{1∈S};
    r_2(S)=(2·1_{1∈S}−1)·1_{2∈S};
    r_3(S)=1_{3∈S}.

This specifies all 60 reward coordinates. Never pays zero, |r_i(S)|≤2,
and the actual own singleton vector is

    (1,−1,−1,1).

No reward normalization, terminal-coordinate shift, or change to Never
is made. In particular such transformations are not presumed to preserve
the face-extension property.

Every player privately and independently samples a stopping time in
ℕ∪{Never}. All players attaining the first finite time form the terminal
coalition. Before absorption the only history is all-Continue, so this
represents all behavioral profiles. Complete unilateral replacements are
arbitrary stopping laws, including unbounded laws and Never. There is no
public correlation or observation of other players' private clocks.

For a parent profile μ write U_i(μ) for terminal payoff, B_i(μ) for the
supremum over all unilateral behavioral replacements, d_i=B_i−U_i, and
E_r(μ)=max_i d_i. For d∈I, r^(−d) is the actual induced reward table on
I\{d}, and μ_−d denotes the unchanged remaining marginal laws. Let
E_(−d)(μ_−d) be their complete terminal exploitability in that game.

**Theorem.** There exists c>0, depending only on the displayed table, such
that for EVERY actual independent behavioral profile μ and EVERY d∈I,

    E_r(μ)+E_(−d)(μ_−d) ≥ c.                         (1.1)

Consequently, if an arbitrary actual ε-terminal equilibrium of any
three-player subgame is extended by ANY independent strategy of its
omitted player, its parent exploitability is at least c−ε. For ε≤c/2
this gives the uniform floor c/2, simultaneously over all four faces,
every child equilibrium, every child payoff target, every calendar, and
every outsider law. The omitted player may be selected afresh at each
accuracy. No best-response or cap-minimization hypothesis is needed.

The positive constant is proved by contradiction sequences. Its numerical
value is not optimized or supplied.

## 2. The parent nevertheless has an explicit exact equilibrium

Let player 3 Quit0 surely. Let each of players 0,1,2 independently Quit0
with probability 1/2 and choose Never with probability 1/2. Then

    U=(1,0,0,1),       B=(1,0,0,1),       E_r=0.       (2.1)

Indeed, for each active i∈{0,1,2}, player 3 forces absorption at date
zero under EVERY replacement of i. Its full response problem has just
Quit0 versus continuing at that date. For player 0 both values are 1;
for players 1 and 2 both values are 0. Thus all pure finite dates, Never,
and arbitrary mixtures have payoff at most the stated cap. Player 3's
reward never exceeds 1, and its prescribed Quit0 attains 1. This checks
its unrestricted deviations too, without assuming opponent absorption.
The same profile is a uniform-equilibrium profile at its terminal target:
active deviations absorb at zero, while no deviation of 3 can deliver a
reward exceeding its prescribed immediate reward 1.

All four players have positive prescribed quit probability. This fact
alone is NOT used to rule out face selection. The literal restrictions
already show why their child incentives differ: after deleting 0, player
1 earns −1/2 and can get 0 by Never; after deleting 1, the same holds for
player 2; after deleting 2, player 0 earns 1/2 and can get 1 by Quit0.
After deleting 3, player 0 still earns 1, but Quit1 earns

    2P(T_2=0)+P(T_1=T_2=Never)=1+1/4.

These are only checks of the displayed profile. The rest of the proof
handles EVERY parent approximate equilibrium and its actual hidden tails.

## 3. Rigidity of every parent approximate-equilibrium sequence

**Lemma.** Suppose μ^n is ANY sequence of actual parent profiles with
e_n:=E_r(μ^n)→0. There are finite dates K_n such that, writing T_i^n for
the independent clocks,

    P(T_i^n<K_n)→0                         (i=0,1,2),
    P(T_3^n=K_n)→1,
    P(T_i^n=K_n | T_i^n≥K_n)→1/2          (i=0,1,2).   (3.1)

No stopping law is asserted to converge to an infinite-strategy limit.
All statements concern these actual profiles at their selected finite
dates, which may escape to infinity.

### 3.1 An actual quantile cut and its uniform error bounds

Set ζ_n=max(e_n,1/n) and α_n=√ζ_n. Ignore finitely many terms so that
0<α_n<1. Player 3's cap is exactly 1 because Quit0 always attains its
coordinate maximum. Its prescribed payoff is the probability it belongs
to the first finite coalition. Therefore

    P(3 is not in the first finite coalition)≤e_n,
    P(T_3^n=Never)≤e_n.                              (3.2)

Here the first event includes all-Never. Choose K_n to be the FIRST
finite date with

    P(T_3^n≤K_n)≥1−α_n.

Such a date exists: P(T_3^n<Never)≥1−e_n>1−α_n. By minimality,
P(T_3^n≥K_n)>α_n, also when K_n=0. For each active i, independence gives

    P(T_i^n<K_n)P(T_3^n≥K_n)
      =P(T_i^n<K_n≤T_3^n)≤e_n.

The event on the left forces finite absorption without 3. Hence

    b_i^n:=P(T_i^n<K_n)≤α_n,
    P(T_3^n>K_n)≤α_n,                                (3.3)

where the second event includes Never.

Define actual conditional laws ν_i^n=law(T_i^n | T_i^n≥K_n), and put

    q_i^n=P(T_i^n=K_n | T_i^n≥K_n),
    p_n=P(T_3^n=K_n).

The conditional laws exist because 1−b_i^n≥1−α_n>0. Conditioning each
active marginal this way changes it in total variation by b_i^n. Couple
old and new marginals independently; the probability any of k altered
coordinates changes is at most the sum of their b_i^n. Since rewards lie
in [−2,2], the payoff difference is at most four times that sum. This
bound holds before taking expectations and for every fixed replacement
of another player.

### 3.2 The finite matching game forced at the quantile

At a date when 3 surely quits, and active independent Quit probabilities
are q=(q_0,q_1,q_2), the active pure-action payoffs are

    Q_0=1,          C_0=2q_2;
    Q_1=2q_0−1,     C_1=0;
    Q_2=2q_1−1,     C_2=0.

Thus the prescribed finite-game payoffs are

    g_0(q)=q_0+2(1−q_0)q_2,
    g_1(q)=q_1(2q_0−1),
    g_2(q)=q_2(2q_1−1).                              (3.4)

For the ORIGINAL actual profile at the selected cut,

    |U_i(μ^n)−p_n g_i(q^n)|≤14α_n,                 (3.5)

and for each actual response a∈{QuitK_n,Never},

    |U_i(μ^n[i←a])−p_n v_i^a(q^n)|≤10α_n,        (3.6)

where v_i^Quit=Q_i and v_i^Never=C_i.

To see (3.5), first condition all three active marginals as above; the
cost is at most 12α_n. If 3 quits before K_n, the first coalition is {3}
and every active payoff is zero. If 3 quits at K_n, the conditional payoff
is exactly (3.4). The event T_3^n>K_n has probability at most α_n and
contributes absolute value at most 2α_n. This proves (3.5). For (3.6),
condition only the TWO unchanged active opponents, costing at most 8α_n.
The replacement QuitK_n or Never cannot precede an earlier anchor. The
same three anchor cases give an additional at most 2α_n. In particular
these are genuine counterfactual estimates, not just prescribed-law ones.

Parent ε-Nash is used with ε=e_n. Equations (3.5)–(3.6) give, for every
active player and both actions,

    p_n[v_i^a(q^n)−g_i(q^n)]≤e_n+24α_n.           (3.7)

In addition, player 0's Quit0 always pays 1 in the ORIGINAL table. Hence
U_0(μ^n)≥1−e_n. Since g_0≤2, (3.5) implies

    liminf_n p_n≥1/2.                              (3.8)

### 3.3 Only a finite-dimensional limit is taken

The finite game (3.4) has unique mixed Nash vector q=(1/2,1/2,1/2).
For example, q_0>1/2 forces q_1=1, then q_2=1, then q_0=0, a
contradiction. Similarly q_0<1/2 forces q_1=0, q_2=0, q_0=1. Thus
q_0=1/2. If q_1>1/2 then q_2=1 and q_0=0; if q_1<1/2 then
q_2=0 and q_0=1. Therefore q_1=1/2. Finally interior q_0 forces
Q_0=C_0, hence q_2=1/2. The half-vector directly satisfies all equations.

Take any convergent subsequence of the four FINITE coordinates (p_n,q^n)
in [0,1]^4. Its limiting p is positive by (3.8). Passing to the limit
in (3.7) says that its q is Nash in (3.4), so q=(1/2,1/2,1/2).
Every subsequential limit has this q, and therefore q^n tends to that
half-vector. Then g_0(q^n)→1; combining (3.5) with U_0≥1−e_n and
p_n≤1 forces p_n→1. Together with (3.3), this proves (3.1).

No payoff or cap is evaluated at a limiting stopping profile. The only
compactness step is the ordinary finite cube for (p,q). All suffixes in
the next section are independently conditioned from actual μ^n.

## 4. The difficult deleted-3 face: hidden tails cannot repair the child

Suppose, for contradiction, that the SAME three active laws μ^n_−3 form
ε_n-terminal Nash profiles of the deleted game, where ε_n→0. Apply
Section 3 to the parent sequence. Define its actual child prefix reach

    A_n=∏_(i=0,1,2) P(T_i^n≥K_n).

By (3.3), A_n≥(1−α_n)^3→1. The independently conditioned child profile
starting at K_n is ε_n/A_n-terminal Nash. Indeed a player can copy its
original law before K_n and replace only the conditional suffix law;
the exact ex-ante payoff gain is A_n times the suffix gain. This is joint
prescribed reach because the player copies its own prefix, not deleted
opponent reach. No approximate subgame perfection is assumed off path.

Its current hazards are q_i^n→1/2. Let

    c_n=∏_(i=0,1,2)(1−q_i^n)→1/8.

Every conditional Continue mass is positive for large n. Independently
condition each child clock once more on being strictly later than K_n,
and shift by K_n+1. This is an ACTUAL three-player tail. The same copied-
prefix argument shows that its terminal Nash error is at most

    ε_n/(A_n c_n)→0.                               (4.1)

Write v_0^n for player 0's prescribed payoff in that actual tail. Its
immediate Quit guarantees exactly 1, so

    v_0^n≥1−ε_n/(A_n c_n).                         (4.2)

At the preceding child root K_n, player 0's Quit endpoint is Q_0^n=1.
Its Continue endpoint, with the literal post-root tail retained, is

    C_0^n=2q_2^n+(1−q_1^n)(1−q_2^n)v_0^n.         (4.3)

The first term counts every row where 2 quits, regardless of 1. The only
remaining continuation case has both opponents Continue. This is not the
finite matching-game C_0=2q_2: removing the anchor genuinely restores the
actual tail term. By (4.2) and q_i^n→1/2,

    liminf_n C_0^n≥1+1/4.

But the child root prescribes Quit with probability q_0^n→1/2. The legal
replacement that always Continues at this row and then uses its original
conditional tail gains exactly q_0^n(C_0^n−1). Approximate child Nash
at reach A_n therefore yields

    q_0^n(C_0^n−1)≤ε_n/A_n→0.                     (4.4)

Equations (4.3)–(4.4) are incompatible. Thus no such simultaneous parent/
deleted-3 approximation sequence exists. Unbounded hidden clocks and
Never were retained throughout; no finite cap truncation or terminal
payoff-only compactification was used.

## 5. The other three faces, for arbitrary approximate profiles

Continue with any parent sequence of vanishing exploitability and the
dates supplied by Section 3. Consider ANY one of its unchanged restrictions.
The first coalition there, with probability tending to one, consists of
player 3 at K_n plus precisely those surviving active players whose clocks
equal K_n. Indeed the anchor is at K_n with probability tending to one,
and the probability any surviving active clock precedes K_n tends to
zero. For each surviving active i, its probability of belonging to this
first coalition therefore tends to

    P(T_i^n=K_n)
      =P(T_i^n≥K_n)q_i^n→1/2.                     (5.1)

All possible later hidden clocks are covered by the vanishing exceptional
event, and rewards are bounded. Consequently:

- Delete 0. Player 1's reward in the child is exactly minus its terminal
  participation indicator. Its payoff tends to −1/2; Never pays 0.
  Its child debt has liminf at least 1/2.
- Delete 1. The same argument applies to player 2.
- Delete 2. Player 0's child reward is exactly its participation indicator.
  Its payoff tends to 1/2, while Quit0 guarantees 1. Its child debt has
  liminf at least 1/2.

Thus none of these unchanged restrictions can have terminal errors tending
to zero either. These are consequences for ALL parent approximate Nash
sequences, not only the single exact equilibrium in Section 2.

## 6. Uniform floor and exact limitation of the architecture

If (1.1) were false for every c>0, choose actual profiles μ^n and omitted
players d_n with

    E_r(μ^n)+E_(−d_n)(μ^n_−d_n)<1/n.

Both errors are nonnegative. Pass to a subsequence with the same d_n=d,
possible because there are only four faces. Section 3 applies to these
actual parent profiles. If d=3, Section 4 contradicts the child error
going to zero; if d=0,1,2, Section 5 does. This proves (1.1).

The result is an exhaustive obstruction to adaptive FACE-PRESERVING
extension: even an omniscient selector of the face, child approximant,
child target, and unrestricted outsider law cannot succeed while retaining
all three child marginal laws unchanged. It does not rule out independent
mixtures of different child laws, changes to surviving clocks, a new
periodic schedule, or a compiler exploiting positive-global-gap ancestry.
In particular the parent itself has zero global minimum debt by (2.1).

## 7. Exact tests and scoped source comparison

As an arithmetic test, the 125 variants of (2.1) obtained by leaving every
active atom 1/2 at date zero and distributing its remaining 1/2 between
date one and Never in increments of 1/8 were enumerated. Every variant is
full exact parent Nash; complete caps were tested at {0,1,2,Never}, retaining
the after-support response. Minimum observed restriction exploitabilities
were (1/2,1/2,1/2,9/64), by omitted player. These finite calculations are
not the proof of the uniform floor; Sections 3–6 allow arbitrary clocks.

The narrow existing cross-face comparisons were:

- [SOCIAL_WEIGHT_REVIEW's proper-face chronology obstruction](SOCIAL_WEIGHT_REVIEW__CARDINAL_FACE_SOURCE_CHRONOLOGY_NO_GO.md):
  independently supplied exact face sources need not nest into a common
  chronology. It does not quantify over every equilibrium on every face
  and every arbitrary outsider extension.
- [FRECHET's quantile common-clock and cross-face regression](CODEX_FRECHET_CYCLE__QUANTILE_COMMON_RECOMBINATIONS_AND_CROSS_FACE_REGRESSION.md):
  simultaneous approximation of all independent recombinations and the
  joint-versus-deleted survival seam are already available. Neither is a
  producer of mixture weights giving small parent debt.
- [SPINOZA's outsider-lift boundary](CODEX_SPINOZA__POSITIVE_REFUSAL_SUPPORT_CARDINALITY_AND_OUTSIDER_LIFT_BOUNDARY.md)
  and [host-release sign reversal](CODEX_SPINOZA__HOST_RELEASE_THREE_PLAYER_NASH_LIFT_SIGN_REVERSAL.md):
  the former warns about selected child/outside-cap incompatibility; the
  latter rules out preserving a specified paid source comparison. Neither
  is the present adaptive all-four-face, all-approximate-child statement.

The original fixed-face note uses a different canonical cyclic table with
an inactive dummy; deleting that dummy and lifting the three-active-player
periodic equilibrium defeats its adaptive extension. Section 2 and the
parent rigidity lemma explicitly address that former shortcut here.

Named Lean source inspections for this argument:

- `UniformEquilibrium/Quitting/Root/LiteralPrefixDeviationTransport.lean`,
  especially `quittingCopyLiteralRootStackThenDeviation` and
  `quittingTerminalPayoff_copyLiteralRootStackThenDeviation_sub_eq`.
  Their exact joint-reach mechanism is the one proved directly for the
  conditioned clock laws in Section 4.
- `UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`,
  `quittingGame_exists_uniformEquilibriumPayoff_threePlayer`: existence of
  a child payoff does not require that its laws extend to a parent Nash.
- `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`,
  `quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance`:
  all full-deviation terminal approximants must share an accepted target
  for that named compiler; no target choice avoids (1.1).

The quantile/finite-cube argument is ordinary mathematics, not an application
of an assumed infinite-strategy compactness theorem. No Lean declaration
for (1.1) is claimed, and no source/export file was changed.

Requested independent check: attack the counterfactual estimates (3.6),
the finite matching-game uniqueness, and especially the two ACTUAL child
conditioning steps in Section 4. The next mathematical question, after
that check, is which operation on surviving laws a genuine cross-face
compiler can justify; mere adaptive choice of the omitted player is now
excluded for this explicit solved table.
