# Strict pivot payoff at every globally constrained observer equilibrium

Identity: CODEX_VARIATIONAL_ESCAPE.

Status: complete ordinary-mathematical argument, internal and awaiting
independent review. No Lean command, export, new UE class, or solution of
Fin4 is claimed. This uses a genuine global constrained minimum and joint
observer repair. It is not a local fixed-calendar test. The existing
all-END and constrained-source notes remain unchanged.

## 1. Exact source and conclusion

Fix a bounded four-player native quitting table Z with Z_i({i})=0 and zero
live and AllNever rewards. Complete private stopping laws are independent;
every unilateral complete replacement, including every finite date and
Never, is allowed. Put

```text
M = max(1, max_(i,S) |Z_i(S)|),
H = closure{(U(P), B(P), N(P), e(P)): P actual},
d_i = B_i-U_i,       nu = product_i N_i,
A = inf{sum_i d_i(P): P actual and nu(P)=0}.
```

B is the full response supremum, e the native Never response, and N the
ORIGINAL Never vector. The closure is in these finite coordinates; its
points need not be actual laws. Assume A>0, choose any distinguished owner
h, and fix 0<r<A. Define

```text
C = {Y in H: d_i(Y)=0 for every i!=h},
J_r(Y) = d_h(Y)+r nu(Y),       m = min_C J_r.
```

AllNever belongs to C. The elementary properification bound

```text
A <= sum_i d_i + 14 M nu^(1/4)                         (1)
```

holds on H. On actual laws, redirect the smallest marginal Never mass to
one finite date. Prescribed values change by at most 2M times that mass;
the mover's cap is unchanged and the other three caps change by at most
2M times that mass. This gives (1); continuity passes it to H. Therefore

```text
0<m<=r<A,       nu(Y)>=((A-r)/(14M))^4>0               (2)
```

at every constrained minimum. To see m>0, a zero minimum would have d_h=0
and nu=0, contradicting (1). In particular the compact minimizing set is
nonempty and every original N_i is positive.

**Theorem.** Every constrained minimum Y satisfies

```text
B_i=U_i>=0 for i!=h,
B_h>m,                  U_h>r nu.                    (3)
```

Let w be the vector

```text
w_i=U_i for i!=h,        w_h=U_h-r nu=B_h-m.          (4)
```

Every exact mixed Nash root of the finite quitting game with continuation
w is AllContinue. Thus w_h is strictly positive, the other entries are
nonnegative, and the critical lowered continuation has no nonzero Nash
root. The strict inequalities hold at EVERY minimizing carrier point,
not only at one selected actual law or one limit of penalized minima.

Neither an inverse-column condition nor all-END activity is needed for this
theorem. Under the known positive-A Fin4 source those additional facts are
available separately. The increment proved here is the exclusion of the
critical constrained face B_h=m, beyond the nonstrict margin obtained by a
vanishing-weight argument.

## 2. Exact joint observer repair by one finite prefix

For a product root q in [0,1]^4, let

```text
H_i(q)=product_(j!=i)(1-q_j),       s(q)=product_j(1-q_j),
Q_i(q)=expected reward when i Quits at this root,
P_i(q)=expected passive reward from nonempty opponent quitting coalitions,
C_i(q;b)=P_i(q)+H_i(q)b_i,
g_i(q;b)=Q_i(q)-C_i(q;b),
R_i(q;b)=max((1-q_i)g_i(q;b), -q_i g_i(q;b)).
```

The displayed expectations use all coalition rewards, including every
participant and passive pair, triple and grand coalition. For a tail point
Y with prescribed vector U and full cap B, the exact prefixed quantities are

```text
U_i'=q_i Q_i+(1-q_i)[P_i+H_i U_i],
B_i'=max(Q_i,P_i+H_i B_i),
N_i'=(1-q_i)N_i,
d_i'=R_i(q;B)+s(q)d_i.                              (5)
```

The maximum prices the whole continuation response menu. No fixed response
attainer is required. Prefixing actual realizing profiles by the SAME
finite root proves (5) on the augmented carrier by continuity. It never
executes a compactified source as an actual infinite tail.

Call q observer-Nash when its three observer coordinates are best replies
in the finite root game with continuation B, while its h coordinate is
arbitrary. For every fixed q_h such roots exist by finite three-player Nash
existence. At an observer-Nash root, R_i=0 for i!=h, so (5) maps C into C
exactly. At a constrained minimum, it follows that

```text
m <= J_r(Y') = R_h(q;B)+s(q)m,
R_h(q;B) >= m[1-s(q)].                              (6)
```

This is a global comparison after a joint repair of all observers at the
new prefix. It does not assume that arbitrary replacement of their entire
old clocks preserves their debts or h's deleted-clock cap.

## 3. Auxiliary root budget and the nonstrict margin

For a>=0 choose any exact four-player Nash root against the continuation

```text
B-a e_h,
```

where e_h here is the coordinate unit vector. Such a root exists by finite
Nash. It is observer-Nash against B, because the other continuation
coordinates are unchanged. Its h-coordinate Nash condition gives

```text
R_h(q;B) <= q_h H_h(q) a.                            (7)
```

Indeed, if q_h=0, its original gap is at most -H_h a and R_h=0. If
0<q_h<1, its original gap is -H_h a and R_h=q_h H_h a. If q_h=1,
its original gap is at least -H_h a and R_h=(-g_h)^+<=H_h a.

Combining (6)--(7), and writing H=H_h(q), gives

```text
m(1-H) <= (a-m)q_h H.                               (8)
```

For 0<=a<m this forces q=0: more directly,
m(1-s)<=a q_h H<=a(1-s), so 1-s=0. AllContinue must therefore be
Nash at B-a e_h. Since native own singletons are zero,

```text
B_i>=0 for i!=h,       B_h>=a.
```

Letting a increase to m proves B_h>=m and gives all the nonstrict claims
in (3). These budget calculations reuse the classical auxiliary-root
argument; the new point below is how its critical face interacts with the
actual constrained minimizing set.

## 4. A zero-cap observer cannot positively block the critical pivot

Suppose a constrained minimum satisfies B_h=m. For each observer i set

```text
Delta_ih = Z_i({i,h})-Z_i({h}).
```

We first prove

```text
B_i=0  implies  Delta_ih<=0.                         (9)
```

Fix eta>0 and take an exact root against B-(m+eta)e_h. The h continuation
is now -eta. Equation (8) becomes

```text
m(1-H)<=eta q_h H.                                  (10)
```

One has q_h>0. Otherwise (10) gives H=1, making the entire root
AllContinue, but h strictly prefers its own singleton zero to -eta.
For each observer j, since H<=1-q_j,

```text
q_j <= 1-H <= (eta/m)q_h.                            (11)
```

Choose eta<m. Every observer's root probability is then strictly below
one. Its Nash condition requires g_j(q;B)<=0.

Now suppose B_i=0 and Delta_ih=D>0. Let j,k be the other two observers.
On the event that neither j nor k quits, the i-gap is q_h D. On the
complement its absolute coalition-gap contribution is at most 2M. Hence

```text
g_i(q;B)
 >= q_h D(1-q_j)(1-q_k)-2M(q_j+q_k)
 >= q_h[D(1-2eta/m)-4M eta/m].                      (12)
```

For eta/m<D/(2D+4M), this is strictly positive, contradicting i's Nash
condition. This proves (9). All inequalities concern actual finite roots;
there is no limiting choice of roots or lower bound on q_h hidden in the
argument. The common factor q_h>0 is retained before division.

## 5. Excluding the entire critical face by a source-level comparison

Let

```text
K={Y in C: J_r(Y)=m and B_h(Y)=m}.
```

If K were nonempty it would be compact. Choose Y in K minimizing ORIGINAL
N_h on K. Equation (2) makes N_h(Y)>0. By (9), every observer with
Delta_ih>0 has B_i>0. Consequently there is a p in (0,1) such that

```text
p Delta_ih <= (1-p)B_i  for all observers i.         (13)
```

For example take p at most 1/2 and strictly below each of the finitely many
positive numbers B_i/(B_i+Delta_ih) for Delta_ih>0. If no such positive
contact occurs, p=1/2 works.

Prefix Y by the root where h Quits with probability p and all observers
Continue. An observer's Quit-minus-Continue value is exactly
p Delta_ih-(1-p)B_i, so (13) makes this root observer-Nash. The h cap
remains max(0,B_h)=m, and its root regret is p m. Equation (5) gives

```text
J_r(Y')=p m+(1-p)m=m,       B_h(Y')=m,
N_h(Y')=(1-p)N_h(Y)<N_h(Y).                         (14)
```

Thus Y' belongs to the SAME compact critical face K but has smaller original
N_h, contradicting its choice. This proves K empty and hence B_h>m at
EVERY constrained minimum. Since d_h+r nu=m,

```text
U_h=B_h-d_h=(B_h-m)+r nu>r nu.
```

The choice of a least-N_h point is made only inside the hypothesized
critical face. The conclusion excludes the entire face, so it does not
replace the theorem's every-minimum quantifier by a selected-source one.

Compactness also gives a fixed eta_r>0, depending on this table, h and r,
such that B_h-m>=eta_r over the whole minimizing set. This is an existence
margin, not a computable universal constant or a new export on its own.

## 6. The critical reduced continuation is completely inert

Take a=m in (8). Since m>0, H_h(q)=1. Thus every observer Continues at
every exact Nash root against B-m e_h. Its h-gap is then

```text
0-(B_h-m)<0.
```

The h coordinate must also Continue. This proves the final assertion at
w in (4). At any a in [0,m] the same conclusion holds; a>m is not claimed.

This root statement does not close the global problem. It identifies a
strict positive pivot payoff and an inert finite continuation at the actual
constrained source. It does not select an absorbing observer-equilibrium
continuation with small h-debt or price a change of the old full laws.

## 7. Topological continuation: a genuine boundary, not a missing section

The separately derived whole-clock continuation theorem in Section 11 of
[the fixed-column note](CODEX_FIXED_COLUMN_VARIATION__FULL_CAP_THINNING_RENT.md)
supplies a compact connected spanning graph of actual exact observer
equilibria along every compact weakly continuous path of proper h clocks.
This strengthens pointwise fixed-clock repair. It does not supply a
continuous equilibrium section or a continuous h-cap.

In the native own-zero case, on such a compact graph K the h-cap is
continuous exactly when its finite-query maxima converge uniformly:

```text
sup_K [B_h-max_(0<=t<=L) V_h(t)] -> 0.
```

The deleted h clock cannot furnish this bound. More basically every profile
on a proper-clock repair graph has nu=0 and d_h>=A, whereas (2) bounds the
entire source sublevel J_r<=r<A away from every proper-clock face in the
retained original-N coordinates. A weak limit that relabels escaping finite
mass as Never is not a path through that augmented carrier sublevel.

The new prefix comparison above avoids this problem by working directly
with the produced compact carrier and an actual finite prefix. It still
does not cross the absorbing debt barrier: the critical face is excluded,
while the interior constrained minimum remains open.

## 8. Source audit, checks, and the precise next question

The existing constrained source, its positive-Never bound, and its inverse-
axis graft live in
[the constrained repair note](CODEX_VARIATIONAL_ESCAPE__CONSTRAINED_REPAIR_AND_CONE_GRAFT_OBSTRUCTION.md).
That note is unchanged. The matrix/weight reduction is in
[the strict-column all-END packet](../exports/FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION.md).
The present theorem does not claim the source construction or auxiliary-root
method as new.

Exact declarations inspected statically:

- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`;
- `quittingTerminalSemanticPair_rootThenContinuation`,
  `continuous_quittingTerminalSemanticPrefix`, and
  `quittingTerminalSemanticPrefix_mem_carrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`
  in `UniformEquilibrium/Quitting/Root/CapNashRootStack.lean`;
- `minimumTerminalSemantic_weightedAuxiliaryNash_budget` and
  `minimumTerminalSemantic_weightedAuxiliaryNash_criticalFace` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticWeightedAuxiliaryNashBudget.lean`;
- `minimumTerminalSemantic_auxiliaryNash_criticalFace` and
  `minimumTerminalSemantic_singletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`.

The implemented budgets assume a weighted global minimum over the full
carrier. They are not directly invoked with zero observer weights: doing so
would drop the constraints defining C. Equations (5)--(8) instead prove the
needed bound using exactly those prefixes which preserve C. The strict
critical-face argument then uses the original Never coordinate and global
constrained minimality. No assertion is made that this ordinary theorem has
been formalized or that an exhaustive library coverage audit has passed.

The owned checker
[CONSTRAINED_PARTIAL_NASH_PREFIX_CHECK](../experiments/CODEX_VARIATIONAL_ESCAPE__CONSTRAINED_PARTIAL_NASH_PREFIX_CHECK.py)
verifies the full finite prefix identity, auxiliary-root regret bound,
critical-face observer estimate and solo-prefix calculation using exact
rational arithmetic. Its algebraic tail controls are explicitly not
claimed to be realizable positive-A examples. The compact global argument
is the proof above, not a consequence of the finite checks.

One precise remaining question is whether the produced strict continuation
w=(U_obs,U_h-r nu), together with the SAME source's full cap data and
inverse-column direction, permits a nonlocal observer-equilibrium return
whose h-regret is less than the absorption loss in (6). Merely finding a
connected Nash graph, or a regular local cap continuation, does not supply
that inequality. No new calibration is proposed here.
