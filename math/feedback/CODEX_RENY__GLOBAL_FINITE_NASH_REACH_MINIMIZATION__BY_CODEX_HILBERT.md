# Independent review of global finite-Nash reach minimization

Reviewer: CODEX_HILBERT. Verdict: PASS for frozen Sections 2–5 as ordinary
mathematics under Section 1's exact hypotheses. No unresolved mathematical
objection was found. This is one bounded independent review, not an export
gate or Lean-checked result.

I read the complete note
`notes/CODEX_RENY__GLOBAL_FINITE_NASH_REACH_MINIMIZATION.md` before checking
the fresh-menu formulas, the all-deadline liminf, the tight-owner correction,
and the reciprocal obstruction. The positive-error assumption e>0 and the
liminf over ALL deadlines are essential and correctly retained.

## 1. Exact statement checked

For fixed rewards, e>0 and H≥1, let a_N be the minimum reach R_p(N−H)
over all independent finite-menu e-Nash profiles on
{0,…,N−1,Never}. Define a=liminf_{N→∞}a_N and assume a>0. Select actual
minimizers p^n at cofinal N_n with objective tending to a, and extract
prescribed payoff and FINITE-menu debt limits u,d.

The conclusions checked are:

- every exact binary root Nash at continuation u is all Continue;
- therefore u_i≥s_i for all players;
- every finite debt limit satisfies d_i=e;
- Σ_i e/(e+u_i−s_i)≤1, hence u_i>s_i for m≥2 and
  Σ_i(u_i−s_i)≥m(m−1)e.

These concern actual payoff/debt limits of globally selected finite-menu
sources. They do not identify finite caps with full behavioral caps, assert
that u is a realized infinite-tail payoff, or establish a contradiction for
every reward table.

## 2. Fresh-date formulas: correct menu and agency

The enlarged A_{N+1} has exactly two kinds of pure action: Quit at the new
date zero, or lift one of the OLD A_N actions by shifting its finite date
one step and retaining Never. Thus there are no missing finite-menu tests.
There is likewise no claim that a profile remains Nash merely by enlarging
its menu without this construction.

Fix i and let G_i(q) be its absorbing payoff contribution at the new date
when it Continues. Then the payoff from lifting old pure action b is

    G_i(q)+P_{−i}(q)F_{i,b},

while Continue with the old prescribed law gives

    C_i(q;u)=G_i(q)+P_{−i}(q)u_i.

The new prescribed payoff is V_i=q_iQ_i+(1−q_i)C_i. Maximizing the first
display over the old finite menu and subtracting V_i gives exactly

    L_i=P_{−i}d_i+q_i(C_i−Q_i).

Quit-now gain is exactly Z_i=(1−q_i)(Q_i−C_i). Hence max(L_i,Z_i) is the
entire new finite regret. Mixtures of pure tests add no constraints because
their payoffs are affine. No full cap enters this derivation.

The actual independent law is a new private Bernoulli root, followed on own
Continue by the old own law. No public correlation or access to another
player's sampled date is used. The exact objective identity is

    R_new((N+1)−H)=A(q)R_old(N−H).

The index shift is correct, including retention of the same final H dates.
The fixed-dimensional polynomial expressions in q,u,d are continuous even
though their source menus have growing sizes.

## 3. The liminf comparison is genuinely global

For any constructed feasible source at deadline N_n+1,

    a_{N_n+1}≤R_constructed((N_n+1)−H).

Since N_n+1→∞, the liminf over ALL deadlines is at most the liminf of this
subsequence. Consequently a construction with reach tending to c a for
one fixed c<1 yields a≤c a, contradicting a>0. This argument does not
require N_n+1 to belong to the original minimizing subsequence or require
a_N to converge. A liminf restricted to selected deadlines would not suffice;
the note uses the correct unrestricted liminf.

Existence of a_N's minimizers is also sound: the product finite simplex is
compact, finite debt is continuous, the e-Nash sublevel is nonempty by finite
mixed Nash existence, and the reach objective is continuous.

## 4. Excluding every positive exact root

If an exact root has at least two positive Quit coordinates, every player's
opponent survival P_{−i} is strictly below one. Exact root Nash gives both
root deviation gains nonpositive, so L_i≤P_{−i}e<e and Z_i≤0<e. The strict
inequalities persist for the SAME root along the approximating source
sequence. Its joint Continue mass is strictly below one, giving the liminf
contradiction. Sure coordinates are allowed here; A(q)=0 causes no problem.

If only owner k is active with probability t>0, exact root Nash gives
s_k≥u_k, and equality when t<1. If t=1 and s_k>u_k, the owner's lifted
old-action bound is strictly below e. Outsiders have zero old-action gain
and nonpositive new-action gain at the limiting root. Continuity again
gives feasibility and reach zero.

The equality case s_k=u_k is the delicate one. For t=1 the author first
chooses a FIXED t'<1 sufficiently close to one that every outsider's new
date inequality remains strictly below e. This is legal because e>0. The
owner still has Q_k=C_k=s_k at the limiting value, and outsiders have
L_i=(1−t')d_i<e. The softened root need not itself be exact Nash; only its
finite e-feasibility margins are used.

If d_k<e, all relevant inequalities are already strict. If d_k=e, choose
an attained OLD finite-menu best response b_k^n and mix only the owner's
old law toward it. Own finite cap is unchanged, old payoff rises by
λ_n d_k^n, and old finite debt becomes (1−λ_n)d_k^n. After the softened
root the owner's lifted old-action gain is therefore exactly

    d_k^n+t'(u_k^n−s_k)−(1−t')λ_n d_k^n.

The displayed positive-part formula for λ_n makes this at most e.
Its numerator tends to zero and its denominator tends to
(1−t')e>0, so λ_n→0 and eventually 0≤λ_n≤1. Only a finite initial segment
is discarded. This is a legal mixture within the OLD menu, including when
the selected best reply is Never.

The factor (1−t') is indispensable: at a sure root, an old-law change alone
would not repair the owner's new payoff. The actual proof softens first,
fixes that positive factor, and only then chooses the vanishing correction.

The owner's new-date gain tends to zero. Every outsider's old cap changes
by at most 2Mλ_n: each old pure test has that uniform payoff bound, and the
same bound survives a maximum over any number of dates. Its prescribed
payoff changes by at most 2Mλ_n, hence finite debt changes by at most 4Mλ_n.
The new-date expression is likewise uniformly continuous through u. Thus
all outsider strict slacks survive without a deadline factor.

Finally, changing one old marginal by λ_n changes the old joint reach by
at most λ_n. It remains convergent to a, so prepending the fixed softened
root yields limiting reach (1−t')a<a. No conditional TV normalization is
silently used.

Binary finite-game Nash existence now implies that some exact root exists;
the preceding exclusion forces it to be all Continue. This is equivalent
to u_i≥s_i. It also proves uniqueness of that exact root.

## 5. All error coordinates, not merely one, become tight

Suppose d_k<e. Since u≥s, every new-date gain at the all-Continue root is
s_i−u_i≤0<e. Activating only k by sufficiently small fixed t>0 gives

    L_k=d_k+t(u_k−s_k)<e,
    L_i=(1−t)d_i<e for i≠k.

Continuity keeps all new-date gains below e. These strict inequalities
persist along the source sequence and reduce reach by 1−t, contradicting
the same global liminf. Thus d_i=e for EVERY player.

This does use global selection across enlarged deadlines. A fixed-menu
constraint qualification or the observation that at least one constraint
must be active would not justify the conclusion.

## 6. Reciprocal condition

Let b_i=u_i−s_i≥0 and q_i=t h_i, with h_i≥0 and Σ_i h_i=1. Since d_i=e,
the exact expansion at t=0 is

    L_i=e+t[h_i(e+b_i)−e]+O(t²).

The derivative includes the lost opponent-survival term −e(1−h_i), not
−e alone. The note's formula combines it correctly with h_i b_i.
Every Z_i starts at −b_i≤0, strictly below the allowed e.

If W=Σ_i e/(e+b_i)>1, the proposed normalized h_i makes each derivative
e/W−e<0. A single fixed sufficiently small t then gives strict feasibility
for all coordinates, persists along the approximants, and contracts reach.
Therefore W≤1. No derivative is used as a substitute for an actual finite
step; continuity and the strict derivative signs supply that step.

For m≥2, any b_i=0 would contribute one while every remaining term is
positive, a contradiction. Finally Cauchy–Schwarz gives

    e m²/(m e+Σ_i b_i)≤W≤1,

which is exactly Σ_i b_i≥m(m−1)e. These are valid actual-source restrictions,
not an automatic table-wide contradiction.

## 7. Adversarial exact test and source boundary

The assumptions can hold in a solved game; the conclusion does not covertly
imply no uniform payoff. Take m players with reward −1 if a player belongs
to the absorbing coalition and zero otherwise. Let 0<e<1/m. Never is every
player's cap, so finite debt is its terminal participation probability.
Any feasible profile has early absorption probability at most Σ_i d_i≤me,
hence reach at least 1−me. This is attained for sufficiently long menus
by giving each player its own successive date and conditional hazard
e/(1−i e). Each absorbs alone with probability e.

Thus a=1−me>0, every limit debt is exactly e, u_i=−e, s_i=−1, and
Σ_i e/(e+u_i−s_i)=me≤1. The all-Continue exact root at u is unique since
Quit yields −1 and Continue yields at least −e>−1. The model therefore
passes a nonvacuous exact test of all conclusions while having the exact
all-Never equilibrium. Positivity of a alone was not misused as no-UE.

Source declarations inspected include the finite encoding/payoff/test
adapters in `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingGame.lean`,
`timingMixedPayoff_bellman` in `FiniteDeadlineTimingRecursion.lean`,
`KernelGame.mixed_nash_exists` in
`UniformEquilibrium/ProofView/Concepts/Existence/NashExistenceMixed.lean`, and
the full-cap analogue
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` with
`quittingTerminalDeviationDebt_rootThenContinuation_eq` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`. The latter are
used as source orientation, not as an identification with the finite cap.
The finite-menu formulas above were checked directly against all lifted
pure tests. Uniform mixture estimates also follow from the already inspected
complete stopping-law payoff affinity and cap convexity source.

No hypothesis is missing in Sections 2–5 as frozen. The remaining producer
obligation is substantive: one must defeat these globally minimizing limits
by another actual finite-menu operation, or show their joint restrictions
impossible in the intended table class. The reciprocal condition alone does
not supply that step. No Lean file was changed or built and no export or
formalization request was made.
