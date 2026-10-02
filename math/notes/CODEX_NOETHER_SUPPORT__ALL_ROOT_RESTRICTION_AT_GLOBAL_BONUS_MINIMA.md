# All-root restrictions at global actual-output bonus minima

Author: CODEX_NOETHER_SUPPORT.

Status: ordinary-mathematics proof of exact root-prefix closure and a
quantitative restriction on EVERY root at actual finite-source minimizers.
Not Lean-checked or exported. No general producer of small A(N,δ), no
unrestricted UE theorem, and no limit-root lower-semicontinuity claim.
This replaces the earlier zero-owner screen as the relevant one-step test;
the [solo-prefix theorem](CODEX_NOETHER_SUPPORT__EXACT_BONUS_NASH_PREFIX_COMPETITION.md)
remains a valid special case.

## 1. Exact source and objective

Fix a bounded canonical Fin4 table r with own singletons s=(1,0,0,0),
zero Never, independent private clocks, and all behavioral deviations.
For F_N={0,...,N−1,Never}, let G_(N,δ) contain all exact finite-game Nash
pairs (ξ,p) with ONLY private planned-Never bonuses ξ∈[0,δ]^4. Define

    A(N,δ)=min_(ξ,p)∈G_(N,δ) E(p),
    E(p)=max_i d_i, d_i=B_i−U_i,
    z_i=p_i(Never), k_i=ξ_i z_i, u_i=U_i+k_i, K=max_i k_i≤δ.

Every B_i is the original COMPLETE cap. Each u_i is the auxiliary menu
cap, since p is exact auxiliary Nash. In the canonical game, a nonpivot's
late response equals Never, so

    B_i≤u_i and d_i≤k_i                 for i≠0.        (1)

This is not a new finite-menu lemma; the exact source declarations are
listed below. K is a transported error bound, not the optimization target.

### 1.1. Law-preserving removal of excess bonuses

There is nevertheless a useful canonical representation of EVERY source
law. Write F_i^max for its original maximum over finite menu dates, W_i
for its original Never response, and P_i=max(F_i^max,W_i) for its original
menu cap. Replace its bonus coordinate as follows:

    ξ̂_i=0                         if z_i=0;
    ξ̂_i=ξ_i                       if 0<z_i<1;
    ξ̂_i=[F_i^max−W_i]_+           if z_i=1.

Then 0≤ξ̂_i≤ξ_i, the SAME law remains exact auxiliary Nash, and

    û_i=U_i+ξ̂_i z_i=P_i.                            (1a)

For a proper player z_i=0, supported finite dates already attain
F_i^max≥W_i+ξ_i, so removing the bonus leaves the support optimal and
P_i=U_i=F_i^max. For a player mixing finite dates with Never, auxiliary
Nash gives F_i^max=W_i+ξ_i, hence P_i=F_i^max=u_i. For a pure-Never
player, auxiliary Nash gives W_i+ξ_i≥F_i^max; the reduced bonus is the
least nonnegative one keeping Never optimal, and its new cap is exactly
P_i. This proves the assertions in every support face, without changing
any player's opponents, actual payoff, or actual complete cap.

Consequently a minimizer of A(N,δ) may ALWAYS be represented with

    û_j=B_j,  k̂_j=d_j                     (j>0).

If E>δ, the pivot is the sole possible maximum debtor and its late
response strictly exceeds its menu cap. Thus

    û_0=B_0−(E−k̂_0),   0≤k̂_0≤δ<E,                  (1b)

so this representation has a NONNEGATIVE lower-cap shift supported only
on the pivot. The arbitrary-representation proofs below remain useful,
but the sign issue can be removed before selecting roots by this exact
law-preserving reduction. No change of the actual optimization target is
involved. This is a direct use of the support equations in the earlier
[bonus elimination calculation](CODEX_NOETHER_SUPPORT__BONUS_NASH_ACTUAL_OUTPUT_EXACTIFICATION.md).

There is also a uniform support consequence of E>δ. The original pivot
late scalar equals E. Since its auxiliary Never response is bounded by
its auxiliary cap,

    U_0≥W_0+ξ_0(1−z_0),
    E=W_0+D_0−U_0≤D_0,       D_0=∏_(j>0)z_j.

Each nonpivot therefore has z_j≥D_0≥E>0. All three of its Never support
equalities hold exactly. In the reduced representation these read

    B_j=W_j+ξ̂_j,       d_j=ξ̂_j z_j,       j>0.       (1c)

The lower bounds on these three Never masses are independent of horizon.
They do not constrain the pivot's own Never mass and do not themselves
equalize a perturbed finite support after opponents are changed.

## 2. Arbitrary exact root and bonus transport

Let q∈[0,1]^4 be ANY exact mixed Nash root of the one-stage quitting game
whose all-Continue payoff is u. Write

    a_i=∏_(j≠i)(1−q_j),       c=∏_j(1−q_j),
    Q_i=expected payoff if i Quits at this root,
    H_i=expected absorbing payoff if i Continues at the root,
    C_i=H_i+a_i u_i,
    n_i=max(Q_i,C_i)=q_iQ_i+(1−q_i)C_i.

H_i includes all nonempty opponent coalitions, but not their all-Continue
event. In particular a_i is opponent-deleted continuation; c is joint
continuation. They must not be interchanged.

Prefix q at a new date zero. Independently for each i, Quit now with
probability q_i; otherwise use its old stopping law shifted by one date.
Never is retained in the shifted tail. Set

    ξ'_i=a_i ξ_i,        z'_i=(1−q_i)z_i.              (2)

The new pair belongs to G_(N+1,δ) EXACTLY. To prove this, each shifted old
finite response has auxiliary payoff H_i+a_iF_i(t); shifted Never with
its new bonus has payoff H_i+a_i(W_i+ξ_i). Every old supported action
therefore attains C_i, and no old action exceeds C_i. The new Quit0 action
has value Q_i. Since q is Nash, its current action and every retained
positive-mass tail action are optimal among these two endpoints. This is
the complete finite normal-form best-response test, not just a prescribed
payoff equality. The argument includes sure quitters and zero a_i.

The new auxiliary payoff and bonus credit satisfy

    u'_i=n_i,         k'_i=c k_i,        K'=c K.        (3)

Indeed the original prescribed payoff is the root expectation at U, so
U'_i=q_iQ_i+(1−q_i)(H_i+a_iU_i)=n_i−c k_i. Adding ξ'_iz'_i=c k_i gives (3).

## 3. Direct full-cap formula: no lower-cap sign assumption

Any original complete response either quits at the new date zero or
waits and then uses an arbitrary old response. Consequently

    B'_i=max(Q_i,H_i+a_iB_i)
         =max(Q_i,C_i+a_i(B_i−u_i)),
    U'_i=n_i−c k_i.                                  (4)

This is valid for suprema that are not attained. Subtracting gives the
EXACT coordinate formula

    d'_i=max(c k_i−(n_i−Q_i),
             a_i d_i−q_i a_i k_i−(n_i−C_i)).         (5)

Here n_i≥Q_i,C_i by root Nash, and c=(1−q_i)a_i. In particular

    d'_i≤c k_i                         (i≠0),
    d'_0≤max(c k_0,a_0d_0),
    E(p')≤max(cK,a_0E(p)).                            (6)

For the nonpivot bound use (1) in the second term of (5), obtaining at
most a_i k_i−q_i a_i k_i=c k_i. Thus every original full response remains
controlled. This proof does NOT assume u_i≤B_i: a bonus can make u_i
strictly exceed a nonpivot's original full cap.

For the actual pivot late scalar L_0=W_0+D_0−U_0, D_0=∏_(j>0)z_j,
the exact transport is

    L'_0=a_0L_0−q_0a_0k_0−(n_0−C_0).                (7)

Indeed W'_0=H_0+a_0W_0 and D'_0=a_0D_0, while U'_0=n_0−c k_0. Formula
(7), not joint-continuation scaling, is the general pivot identity.
The solo-nonpivot case has q_0=0 and n_0=C_0, recovering its exact scaling.

## 4. Quantitative restriction on ALL roots at global near-minimizers

Fix δ≥0 and put b_δ=inf_(N≥1) A(N,δ). Assume b_δ>δ. At any finite
actual-output minimizer (ξ,p) of A(N,δ), every exact Nash root q against
its auxiliary continuation u satisfies

    b_δ≤A(N+1,δ)≤a_0 A(N,δ),
    1−∏_(j>0)(1−q_j)≤(A(N,δ)−b_δ)/A(N,δ).          (8)

Proof: K≤δ<b_δ≤A(N,δ), and c≤a_0, so (6) gives the middle comparison.
The root and the resulting law/bonuses were arbitrary. Thus (8) controls
the SUPREMUM of nonpivot root activation over the entire Nash-root set,
not only one chosen branch.

If A(N,δ)=b_δ is attained at a finite horizon, every exact root has
q_1=q_2=q_3=0. Without such attainment, for any actual minimizing sequence
with A(N_k,δ)→b_δ, the maximum nonpivot activation among ALL exact roots
at each u^k tends to zero. Horizons may vary arbitrarily. The same argument
applies to δ_k→0 with b_(δ_k) bounded away from zero, provided the chosen
finite minima approach their corresponding b_(δ_k).

This is a necessary condition within the exact bonus-Nash search family.
It is not a raw-table impossibility theorem or a proof that b_δ=0. It
does not replace the actual E objective by K or deleted Never mass.

## 5. The pivot-only case is genuinely separate

When a root only activates pivot 0, a_0=1 and c=1−q_0, so (6) need not
contract its unrestricted debt. Its endpoints are Q_0=1 and C_0=u_0.
The cases are:

- If u_0>1, root Nash forces q_0=0.
- If u_0=1, any permitted q_0 may be positive. Formula (7) becomes
  L'_0=L_0−q_0k_0. With k_0=0, pivot late error is unchanged even though
  the root has positive prescribed absorption.
- If u_0<1, root Nash forces q_0=1. The full cap becomes max(1,B_0) and
  the prescribed pivot payoff becomes one. Thus its new debt is
  [B_0−1]_+<d_0 whenever d_0>δ≥k_0, since U_0=u_0−k_0<1. All nonpivot
  debts vanish by c=0. There is a stronger raw-table conclusion below.

Therefore, at a finite attained positive horizon-global minimum, u_0≥1;
and any positive pivot-only root when u_0=1 must have q_0k_0=0. These
conclusions do not justify treating pivot-only absorption as nonpivot
deleted-survival contraction. A nonattained limiting statement needs its
own quantitative control and is not inferred just from these strict cases.

### 5.1. A sure-pivot-only root closes the branch completely

Define the three raw joining gains

    γ_j=r_j({0,j})−r_j({0}),             j>0.

If q=(1,0,0,0) is a root Nash equilibrium at ANY continuation, the
nonpivot best-response inequalities give γ_j≤0 for every j>0. Conversely,
these three inequalities alone make the literal original profile

    pivot Quit0 surely; every nonpivot Never

an exact FULL terminal equilibrium. The pivot gets one, and any later
finite deviation gets one while Never gets zero. A nonpivot gets r_j({0});
Quit0 gets r_j({0,j})≤r_j({0}), and every later finite date or Never gets
r_j({0}). Mixtures of these responses cannot improve. Thus the profile
is also a zero-bonus finite-menu equilibrium and A(1,δ)=0 for every δ≥0.

In particular, if every exact root at a source continuation has no active
nonpivot and u_0<1, existence of a root forces the sure-pivot root and
solves the original game by this one-date profile. The same conclusion
holds at u_0=1 IF a sure-pivot-only root exists; a mixed pivot-only root
need not supply the three raw inequalities. This is a source-level branch
test, not a new equilibrium class. The parent coordinator suggested testing
the raw join inequalities rather than stopping at strict prefix improvement.

### 5.2. Quantitative exclusion of values bounded below the singleton

Suppose γ=max_(j>0)γ_j>0, so the preceding pure profile is unavailable.
Fix M≥1 bounding every |r_i(S)|. Any auxiliary continuation from the
bonus box satisfies |u_i|≤M+δ. Put

    ρ=1−∏_(j>0)(1−q_j).

For EVERY exact root at a source with u_0<1,

    ρ≥min((1−u_0)/(4M+δ), γ/(4M)).                  (9)

Here is an elementary proof, retaining strict inequalities correctly.
If ρ<(1−u_0)/(4M+δ), then

    |Q_0−1|≤2Mρ,
    |C_0−u_0|≤(2M+δ)ρ,
    Q_0−C_0≥1−u_0−(4M+δ)ρ>0.

Thus root Nash forces q_0=1. Choose j with γ_j=γ. With the pivot now
sure, the difference between j's Quit and Continue endpoints is γ unless
some other nonpivot quits. Each endpoint then changes by at most 2M, so

    Q_j−C_j≥γ−4Mρ.

If also ρ<γ/(4M), player j must quit surely. This makes ρ=1, contradicting
ρ<γ/(4M)≤1/2. No root can have ρ below both thresholds, proving (9).

At any finite minimizer from Section 4, write t=(A(N,δ)−b_δ)/A(N,δ).
If t<γ/(4M), (8), (9), and Nash existence give

    u_0≥1−(4M+δ)t.                                  (10)

For u_0≥1 this is immediate; otherwise (9) and ρ≤t force the first term
of its minimum to be at most t. Consequently a positive horizon-global
minimum cannot have a near-minimizing sequence with u_0 bounded strictly
below one. The statement is wholly finite-source quantitative. It does
not claim that all roots at a limiting continuation arise as limits of
source roots, and it leaves the equality and above-singleton branches open.

## 6. Small exact simultaneous-root test with nonzero bonuses

For every nonempty S set

    r_0(S)=1 if 0∈S and 1∉S, else 0;
    r_1(S)=1 if {0,1}⊆S, else 0;
    r_2(S)=r_3(S)=0.

This is a complete canonical table. In F_1 let each of 0,1 Quit0 with
probability one half and otherwise Never, with 2,3 always Never. Set
ξ=(1/2,1/2,0,0). For players 0 and 1 their original Quit0 values are
1/2, their Never values are zero, and their prescribed values are 1/4.
Both auxiliary endpoints are 1/2. Thus the profile is auxiliary Nash with

    u=(1/2,1/2,0,0),     E=K=1/4.

Now choose q=(1/2,1,0,0). At continuation u, player 0 has Q_0=C_0=0;
player 1 has Q_1=1/2>C_1=1/4; other payoffs are zero. This is exact root
Nash with two active coordinates. Transport gives

    a_0=0, a_1=1/2, c=0, ξ'=(0,1/4,0,0),
    u'=U'=(0,1/2,0,0), E'=0.

The surviving positive ξ'_1 is legitimate although its new Never mass is
zero. Formula (4) directly gives B'=U'. This checks joint versus deleted
continuation and the sure-owner boundary; it is only an algebraic test,
not a new solved class.

## 7. Source comparison, limit boundary, and next investigation

The exact private-Never bonus transport (2) is the additional closure fact.
The ordinary root payoff and full-cap recursion is already available in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean` and was used in
[RENY's maximum-debt note](CODEX_RENY__MAXIMUM_DEBT_MINIMUM_TIES_AND_ACTUAL_ROOT_UNIQUENESS.md).
That note treats a global minimum over ALL actual laws, where one-coordinate
repair excludes a unique maximum debtor. Such a repair need not preserve
G_(N,δ); its all-Continue-root uniqueness conclusion cannot simply be
imported to this restricted objective.

The exact declarations `singlePivot_nonpivot_fullCap_eq_menuCap`,
`singlePivot_pivot_fullCap_eq_max_menu_never_add_deletedNever`, and
`singlePivot_fullExploitability_eq_max_menuExploitability_scalar` were read in
`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`.
They supply the finite-menu/full-response split used in (1), not a selector.

`quittingTerminalSemanticDebt_prefix_le_auxiliaryNashDefect` and its exact
version were read in `UniformEquilibrium/Quitting/Terminal/AuxiliaryNashDebt.lean`.
They assume a nonnegative coordinate shift h and use continuation B−h.
Here B_i−u_i may be negative for a nonpivot, so that lower-cap ledger does
not apply directly. Equations (4)–(5) deliberately establish the required
comparison without its sign hypothesis. Section 1.1 separately shows how
to reduce excess bonuses first and obtain a law-preserving representation
where the sign hypothesis is valid and the shift is supported only on the
pivot. No new formalized theorem is claimed.

The limit-root issue remains important. Compactness of u^k and of the
finite root cube supplies limits of CHOSEN exact roots. It does not ensure
that every exact root at a limiting u* is approximated by roots at u^k.
Thus (8) does not prove that G(u*) has no nonpivot-active root; a new root
could appear at a degenerate boundary. No lower-semicontinuity assumption
is smuggled into the all-root finite-source statement.

Next question: combine the original menu support/complementarity conditions
with (8) to obtain a joint-law competitor at a positive limiting minimum.
One must either exploit finite-source roots directly or justify persistence
of the desired root under bonus/law variation. An all-Continue limit, an
exact-zero-owner assumption, or one nonrenewable prefix does not settle
the original arbitrary-canonical small-E question. Controlled approximate
prefixes are also allowed by that original question, even if they leave
the exact auxiliary-Nash family.
