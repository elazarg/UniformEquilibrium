# Finite mixed roots on the same two-pinned polynomial face

Author: CODEX_TARSKI_PREMIUM.

Status: complete bounded ordinary-mathematics test, not independently reviewed
or Lean-checked. It retains the actual minimizing annotation of the universal
root-potential problem, not a reward-table or behavioral-law minimum. The
entire pair-supported exact-root operation fails to return to the upper
singleton box unless it already produces a repeatable two-sure Nash root.
This is not an obstruction to arbitrary finite roots or a new UE class.

## 1. Same annotation and exact question

Use the arbitrary four-player bounded table, root quantities Q,C,F,a,
and C¹ all-exact-root drift assumption (D) in
[the boundary-gradient checkpoint](../notes/CODEX_TARSKI_PREMIUM__UNIVERSAL_ROOT_DRIFT_FORCES_NEGATIVE_RECIPROCAL_PAIR.md).
Let x minimize H on the lower boundary L of C=∏_k[s_k,B]. No annotation
is required to be an attainable behavioral payoff or cap. Suppose its
lower-pinned set is exactly J={i,j}, so

    x_i=s_i, x_j=s_j, and x_k>s_k for k∉J.

The proved same-point gradient inequalities give, with g=∇H(x),

    g_j(s_j−r_j({i}))≥1,
    g_i(s_i−r_i({j}))≥1,
    g_i,g_j≥0.

Hence both gradient coordinates are strictly positive and

    r_i({j})<s_i,          r_j({i})<s_j.                (1)

Unlike mere negative reciprocal sum, (1) identifies strict negative cross
singletons in BOTH directions at this actual two-pinned face.

Test EVERY product root q supported on this pair: q_k=0 for k∉J, and
q_i,q_j range independently over the whole interval [0,1]. Keep the
annotation equal to the SAME x. Require full four-player root Nash, not
just Nash of the active pair. In particular, every outside player's
immediate joining test is retained. Can a root of positive absorption have
its exact successor w=F(q,x) in L, contradicting H-minimality there?

**Exact result.** Under (1), if such a root is Nash and w∈C, then
q_i=q_j=1. It is consequently root Nash against EVERY annotation, yields
an actual exact terminal Nash pure pair, and is a positive-charge
self-loop at its own terminal payoff. Thus (D) forbids it. Every nonzero
pair-supported exact Nash root at this two-pinned minimizer must therefore
send at least one coordinate below its singleton floor. In particular no
one of these eligible successors lies on L.

## 2. All finite probabilities and collision rewards retained

Put u=q_i and v=q_j. For owner i, the actual root endpoints at x are

    Q_i=(1−v)s_i+v r_i({i,j}),
    C_i=(1−v)s_i+v r_i({j}),
    Q_i−C_i=v[r_i({i,j})−r_i({j})].                    (2)

The analogous j formulas interchange i,j and u,v. These keep the literal
collision rewards; neither a normalized matrix direction nor stationary
equilibrium is substituted for finite root Nash.

If u=0<v, owner i is prescribed Continue and

    w_i=s_i+v[r_i({j})−s_i]<s_i

by (1). Thus w∉C. The case v=0<u is symmetric. The case u=v=0 has zero
charge and is not a proposed strict successor. All zero-probability cases
are now exhausted without division.

Suppose u,v>0 and w∈C. Since owner i uses Quit with positive probability,
exact Nash implies w_i=Q_i: if it also Continues, its two endpoints tie;
if it Quits surely, Q_i is its prescribed best value. Equation (2) and
w_i≥s_i therefore imply

    r_i({i,j})≥s_i>r_i({j}).                            (3)

Since v>0, (2) makes Quit STRICTLY better than Continue. Exact root Nash
therefore forces u=1. The same argument forces v=1. This proves the
full-family assertion, including every genuinely mixed and one-sure case.

## 3. Exact sure-root exit, not an assumed repeatability principle

Now the selected product root is the pure pair {i,j}. Against any one
player's unilateral root change, a member of the pair still Quits surely.
Every action endpoint is therefore independent of the continuation
annotation. The full root Nash tests already include each outside player's
joining reward r_k({i,j,k}) versus r_k({i,j}); no outside incentive has
been silently added as a premise or dropped from the proof.

It follows that this SAME root is Nash at the actual behavioral punishment
vector P, regardless of whether its coordinates are jointly attained.
Hence it supplies the finite sure-root alternative from the polynomial
characterization. More directly, have i and j Quit at date zero and all
others Never. Every complete unilateral behavioral response is screened at
date zero by a different sure owner, so this is actual exact terminal Nash.

Repeatability is valid here for an additional explicit reason. At the
annotation y=r({i,j}) the root is still Nash, and F(q,y)=y with a(q)=1.
Thus the all-edge potential would require H(y)−H(y)≥1, impossible. Both y
and x lie in the padded box. This does NOT assert that an arbitrary
one-sure root at P repeats against its own payoff; the production
SureRootNonrepeatability example refutes that broader assertion. Here TWO
sure players eliminate the annotation from every unilateral endpoint.

## 4. Scope and the next genuine finite operation

The no-sure alternative makes the sure exit unavailable; even without it,
the assumed universal H independently rules out the resulting charged
self-loop. Consequently the pair-only finite operation cannot prove a
new same-face descent by locating a boundary successor. The precise cause
is the forced strict cross-singleton losses (1): any nonsure eligible
pair root remains below a singleton somewhere, while a successor above
all singletons forces both active players to be sure.

No arbitrary solved-profile counterexample or numerical root search is
needed for this obstruction. It holds at the actual H-minimizing face,
for ALL pair probabilities and ALL full root Nash tests. It neither
excludes the universal polynomial in the remaining mixed-sign case nor
shows that all eligible roots are pair-supported.

The next operation must recruit a player outside this two-pinned set or
use a face with at least three pins. Its finite collision terms and the
same annotation must remain explicit; merely repeating the negative-pair
projection or treating a restricted pair equilibrium as a four-player
Nash root would not address that task.
