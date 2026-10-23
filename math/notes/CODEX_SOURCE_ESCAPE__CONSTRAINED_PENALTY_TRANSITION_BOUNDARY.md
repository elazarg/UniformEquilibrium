# Exact limits of penalty and reward homotopies at a positive-gap source

Identity: CODEX_SOURCE_ESCAPE.

Status: complete ordinary mathematical deductions from the existing
constrained source; internal, not exported and not checked in Lean.
The scalar penalty, positive recipient weights and constant absorbing
offsets do not supply a new native deformation. A genuinely changing
own-containing-set deformation has either universal gap-monotonicity
direction if and only if the whole native absorbing-gap obligation is
already solved. The additional universal transformation classification is
coordinatewise and profilewise; it does not classify source-specific
gap-preserving maps. These results retire particular inferences and supply
neither a new reward-table exclusion nor a positive-gap example.

## Exact setup

Use the fixed four-player native table, full stopping-law cap, and original
Never carrier of
[the constrained source note](CODEX_VARIATIONAL_ESCAPE__CONSTRAINED_REPAIR_AND_CONE_GRAFT_OBSTRUCTION.md).
In particular, own singleton, live, and literal AllNever rewards are zero;
all complete unilateral stopping laws are allowed; the carrier retains
`(U,B,N,e)` and is the closure of actual profiles. Set

```text
M = max(1, max |Z_i(S)|),
A = inf { sum_i (B_i-U_i) : actual profile, product_i N_i=0 } > 0,
C_h = {Y in the carrier : B_i-U_i=0 for every i!=h},
nu(Y) = product_i N_i,
J_r(Y) = B_h-U_h+r nu(Y),
m_h(r) = min_(Y in C_h) J_r(Y),                    r>=0.
```

The compact set `C_h` contains AllNever. The same fixed native table has an
invertible singleton matrix with a strictly positive column

```text
v = Gamma^(-1)e_h > 0,       S = sum_i v_i,       k = S-v_h > 0.
```

This column is an additional premise for the explicit bound below. The
strict-column source produces at least one such `h` from an actual Fin4
positive absorbing gap; it does not produce every column as positive.

## 1. The relevant threshold is the attained value, not the penalty

For every `r>0`, `m_h(r)>0`. Indeed a zero minimum would have both all debts
zero and `nu=0`, contradicting the existing properification inequality

```text
A <= sum_i (B_i-U_i) + 14M nu^(1/4).
```

At a minimizing point, the same inequality gives

```text
A <= m_h(r)-r nu+14M nu^(1/4)
  <= m_h(r)+14M nu^(1/4).
```

Consequently, whenever `m_h(r)<A`, every minimizing point satisfies

```text
nu >= ((A-m_h(r))/(14M))^4 > 0.                    (1)
```

Thus every original marginal Never coordinate is positive. All conclusions
of the existing strict critical-face proof hold in this larger parameter
range:

```text
B_i=U_i>=0 for i!=h,
B_h>m_h(r),
U_h>r nu,
```

and the finite root game with continuation
`w_i=U_i` for `i!=h`, `w_h=U_h-r nu` has only AllContinue as an exact Nash
root. To check this extension, the original proof uses `r<A` only to obtain
positive original Never mass. Its prefix budget, auxiliary-root argument,
zero-cap observer estimate, and least-original-`N_h` comparison use the
positivity of `m_h(r)` and (1), not `r<A` separately. The same observation
extends the all-END conclusion and `N_h<=1/(1+rS)` from the constrained
inverse-column graft proof.

This is not a new proof of those results. It identifies their exact parameter
hypothesis and prevents an invalid use of `r=A` as an exit from that hypothesis.

## 2. An explicit interval extends strictly beyond r=A

The complete inverse-axis tail already proved in the source note gives

```text
m_h(r) <= Phi_h(r)
       = v_h/(S k) * [1-(1+rS)^(-k/v_h)].           (2)
```

Write `c_h=v_h/(S k)`. The derivative calculation is

```text
Phi_h(0)=0,
Phi_h'(r)=(1+rS)^(-S/v_h) < 1        for r>0.
```

It follows that

```text
0<Phi_h(r)<r,                       r>0,
Phi_h(r) increases to c_h.
```

Also `A<=c_h`. This follows by taking the inverse-axis tails with horizon
`T` tending to infinity in the same original carrier: their observer debts
are zero, their h-debts tend to `c_h`, and their joint Never tends to zero.
Applying the properification inequality before taking the limit proves the
claim without asserting that a compact continuous-time tail is itself an
actual discrete strategy.

At `r=A`, (2) gives

```text
m_h(A) <= Phi_h(A) < A.
```

In particular, all the strict source conclusions in Section 1 still hold,
and every minimizing point has the explicit common bound

```text
nu >= ((A-Phi_h(A))/(14M))^4 > 0.                   (3)
```

There is in fact a nonzero interval beyond `A` with the same property. If
`A<c_h`, define

```text
R_h = [(1-A/c_h)^(-v_h/k)-1]/S.
```

Then `R_h>A`, and every `0<r<R_h` satisfies `Phi_h(r)<A`; all conclusions
of Section 1 apply with the explicit replacement of (1) by

```text
nu >= ((A-Phi_h(r))/(14M))^4 > 0.
```

If `A=c_h`, the same conclusion holds for every finite `r>0`. These statements
leave open the possible limiting behavior as `r` tends to infinity. They do
not show that a positive absorbing gap exists, or that a finite first
transition must exist.

## 3. The value function does not provide the missing transition

The compact lower-envelope definition implies that `m_h` is nondecreasing,
concave and 1-Lipschitz, with `m_h(0)=0`. More precisely, if `K_r` is its
compact minimizing set, then

```text
(m_h)'_+(r) = min_(Y in K_r) nu(Y),
(m_h)'_-(r) = max_(Y in K_r) nu(Y)       for r>0.     (4)
```

For the right derivative, compare `m_h(r+t)` with a minimizer at `r` having
least survival to get the upper bound on the secant slope. A minimizer at
`r+t` gives the lower bound by its own survival. Every compact limit of such
minimizers as `t` decreases to zero minimizes at `r`, by continuity. This
proves the reverse bound and hence the first identity. The left-hand proof
uses the maximum instead. Concavity also ensures both one-sided derivatives
exist; the argument needs no unique or continuous selection of minimizers.

Combining (1) and (4) shows that the right derivative remains strictly
positive whenever `m_h(r)<A`. It does not force a critical cap face or a
finite absorbing transition. In particular, any minimizing source with
`nu=0` would have `m_h(r)>=A`, and hence can occur only beyond the interval
proved in Section 2.

A homotopy in `r` therefore does not manufacture the equation `B_h=m_h(r)`
excluded by the previous theorem. A homotopy of reward tables cannot be
substituted without a separate proof that its original absorbing gap stays
positive and that its selected carriers retain the required source data.
Continuity of the gap under small reward changes only supplies local
preservation, not such a complete path.

## 4. The exact row-affine orbit does not change the native problem

For an actual profile P, write `e_i` for its pure-Never response,
`H_i=product_(j!=i)N_j`, and `nu=product_i N_i`. At the own-zero native
table, the payoff of finite pure Quit date k tends to `e_i` as k tends
to infinity: any surviving own singleton pays zero. Therefore the
supremum B_i over all finite dates already includes e_i.

Add a signed constant c_i to EVERY nonempty absorbing reward in row i,
with live and Never still zero. Every finite-date response increases by
c_i; the Never response increases by `c_i(1-H_i)`. Consequently the exact
formula for every actual profile is

```text
U_i^c = U_i+c_i(1-nu),
B_i^c = c_i+max(B_i,e_i-c_i H_i),
d_i^c = max(B_i,e_i-c_i H_i)-U_i+c_i nu.             (5)
```

In particular, for `c_i>=0`,

```text
B_i^c=B_i+c_i,       d_i^c=d_i+c_i nu.              (6)
```

These formulas are full-response suprema, including Never. On every
absorbing profile, nonnegative offsets preserve each debt exactly,
whereas arbitrary signed offsets can only increase each debt:

```text
nu=0  implies  d_i^c>=d_i,
c_i>=0 and nu=0  implies  d_i^c=d_i.               (7)
```

For arbitrary positive recipient weights `a_i`, the table
`R_i(S)=a_i Z_i(S)+c_i` has the corresponding formula with U, B and e
multiplied by a_i. If all c_i are nonnegative, its entire absorbing debt
set is exactly the positive diagonal image of the original one. Thus

```text
A_abs(R)=inf_(P absorbing) sum_i a_i d_i(P),
(min_i a_i)A <= A_abs(R) <= (max_i a_i)A.           (8)
```

There is also a useful bound at every boundary of the positive weight
cone:

```text
(min_i a_i)A <= A_abs(diag(a)Z) <= 2M min_i a_i.    (8a)
```

For its upper bound, choose h with least a_h. Set h's prescribed hazard
to one at date 0, and choose a mixed Nash equilibrium of the finite
three-observer first-stage game with this sure quitter fixed.
Under every observer's complete replacement, h still quits at date 0.
Each observer's full cap is therefore its one-stage cap, and its debt
is zero. The pivot's prescribed payoff and full cap both lie in
`[-M,M]`, so its debt is at most 2M. This actual absorbing profile proves
the bound. At a zero weight the pivot row is identically zero and the
same construction is itself exact absorbing terminal Nash. Thus a
weight path to a solved zero-row boundary necessarily loses its native
absorbing gap; it does not retain a uniform positive source margin.

Signed offsets have an exact sign division under the positive native
gap assumption. First take unit weights. If any c_h>0, then (5), the
nonnegativity of every new debt, and (6) at h give, with
`D^c=sum_i d_i^c` and `Cminus=sum_i max(-c_i,0)`,

```text
nu <= D^c/c_h,
D <= D^c+Cminus nu <= (1+Cminus/c_h)D^c,
A <= (1+Cminus/c_h)D^c+14M(D^c/c_h)^(1/4).         (8b)
```

Thus the unrestricted full SUM debt of the shifted game is bounded
positively away from zero, even when other offsets are arbitrarily
negative. Positive weights are handled by applying this argument to
the scaled native table, whose absorbing gap is positive by (8).
If instead all c_i are nonpositive, AllNever is exact terminal Nash
in the shifted game, since every solo Quit pays c_i<=0.
This can coexist with a positive absorbing gap.
Hence the entire row-offset orbit has no UE when `max_i c_i>0`
and has the AllNever equilibrium when `max_i c_i<=0`, conditional on
the fixed native A>0. A solved nonpositive-offset endpoint is therefore
not a contradiction to the original native source.

The infinite negative-offset limit has an explicit vanishing channel for
the unrestricted full SUM-debt infimum Delta_all.
Fix `c_h=a>0`, set every observer offset to `-K` with K>0, and put
`kappa=max_(i!=h) max(0,-Gamma_ih,Z_i({i,h})-Gamma_ih)`.
Under A>0 one has kappa>0, since kappa=0 would make the pure solo-h
profile native absorbing Nash. Prescribe h to Quit at date 1 with
probability `1-x` and Never with probability `x=kappa/(K+kappa)`;
all observers Never. An observer's native cap rent above Never is
`(1-x)max(0,-Gamma_ih,Z_i({i,h})-Gamma_ih)`, at most Kx.
Its shifted Never response therefore attains its full cap. The resulting
actual profile has

```text
d_i^(Z+c)=0  (i!=h),       d_h^(Z+c)=a x,
0<Delta_all(Z+c)<=a kappa/(K+kappa) -> 0.           (8c)
```

The usual uniform positive own raise in the source construction means
addition to every nonempty entry; it is precisely (6), not a change only
at the singleton. After subtracting the new own singleton, the native
table of R is `a_i Z_i(S)`. Its singleton matrix and carrying column are

```text
Gamma^a=diag(a)Gamma,       v^a=v/a_h.              (9)
```

All inverse-column signs and the sign of the determinant are unchanged.
No new passive or joining-contact geometry is reached.

There is a stronger statement for the exact constrained source.
Let `T_a(U,B,N,e)=(aU,aB,N,ae)` be the canonical homeomorphism between
the native carriers. Positive scaling preserves the observer-zero
condition exactly, since `d_i^a=a_i d_i`. Its minimum, minimizers and
inverse-axis bound obey

```text
C_h^a=T_a(C_h),
m_h^a(r)=a_h m_h(r/a_h),
argmin_(C_h^a) J_r^a = T_a(argmin_(C_h) J_(r/a_h)),
Phi_h^a(r)=a_h Phi_h(r/a_h).                       (10)
```

The other three weights have no effect on this constrained optimization.
The strict pivot margin is merely multiplied by a_h after the same
parameter change. A positive offset only in the pivot row adds exactly
`c_h nu` to its debt, giving the same scalar penalty once again. Positive
offsets in observer rows instead add `c_i nu` to their debts; one cannot
silently impose zero raised observer debt on a positive-Never native
source. Normalizing those rows first returns to (10).

Thus every finite composition of these row-affine operations either
leaves the native problem unchanged up to positive row weights or
reparameterizes the already analyzed penalty. This conclusion uses the
whole profile and constrained carrier, rather than a particular chosen
minimizer.

## 5. Maximality of universal additive coordinatewise transport

Here is an exact limit on enlarging the preceding class by a fixed
additive correction. Fix a player i and a finite row W_i(S). The following
are equivalent:

1. For every own-zero native table Z and every absorbing product profile P,
   `d_i^(Z+W)(P)>=d_i^Z(P)`.
2. W_i(S) is one constant c_i for all nonempty S.

The constant may have either sign. Equality for every such Z,P holds if
and only if this constant is nonnegative.

To prove necessity, fix a nonempty coalition T avoiding i. Let every
member of T quit surely at date 1 and all other opponents Never.
Player i has exactly three response-payoff classes:

```text
Quit at date 0:      0,
Quit at date 1:      b=Z_i(T union {i}),
Quit later/Never:   a=Z_i(T).
```

The corresponding added rewards are
`w0=W_i({i})`, `wJ=W_i(T union {i})` and `wT=W_i(T)`.
Prescribe date 0. Choosing `(a,b)=(K,-K)` with K arbitrarily large makes
the native and perturbed caps select a; monotonicity then forces
`wT>=w0`. Choosing `(-K,K)` forces `wJ>=w0`.
Next take `a=b=-K`. Prescribing Never and choosing K sufficiently large
makes the early singleton the unique best response and forces `w0>=wT`.
Prescribing date 1 similarly forces `w0>=wJ`.
All these prescribed profiles absorb surely, including the one in which
i uses Never. Hence `w0=wT=wJ`. Varying T covers all nonempty coalitions.

Sufficiency is (7). For the equality characterization, nonnegative c_i
works by (7). If c_i<0, use the zero table with i the sole sure quitter
and all opponents Never. The original debt is zero; after the offset,
prescribed payoff is c_i and Never gives zero, so the new debt is -c_i>0.

The same argument, after positive scaling, classifies fixed affine
transformations satisfying the coordinatewise comparison
`d_i^(aZ+W)(P)>=a_i d_i^Z(P)` universally. This is a classification of
universal same-profile coordinatewise debt transport. It does NOT rule
out a SUM-only argument, a different-profile construction, a correction
depending on the particular source table, or a deformation that preserves
the positive gap by a separate global theorem.

## 6. Either universal monotonicity of the own-containing homotopy is the conjecture

The own-containing-set shift really does move the native game. Raising
row i by t on coalitions containing i and then subtracting its new own
singleton gives the native deformation

```text
(H_t Z)_i(S)=Z_i(S)-t 1_(i notin S).                (11)
```

Here t may be any finite real. These maps form an additive group:
`H_s(H_t Z)=H_(s+t)Z`. They satisfy

```text
Gamma_ij(t)=Gamma_ij-t  (i!=j),
delta_i(T;t)=delta_i(T)+t  (T nonempty).            (12)
```

This is distinct from the row offset in (5). The corresponding root
endpoint identity is the own-set shift studied in
`ownShiftReward` and `quittingRootEndpointDifference_ownShiftReward`
in `UniformEquilibrium/Quitting/Root/EndpointBackwardStability.lean`.
That file explicitly treats a fixed continuation, not a transported
global tail or absorbing-gap theorem.

Write `A_Z(t)=A_abs(H_t Z)`. For every native Z, the AllQuit profile gives
the global bound

```text
0<=A_Z(t)<=sum_i (-delta_i(I\\{i})-t)^+.             (13)
```

Thus `A_Z(t)=0` for all sufficiently large t. No positive-gap assumption
is used: a deviator who Continues faces the other three sure quitters,
so the displayed positive part is its complete regret.

There is also a solved endpoint in the opposite direction. Fix any h
and choose

```text
R>max(0,max_(i!=h) delta_i({h})).
```

At `H_(-R)Z`, prescribe h to Quit surely at date 0 and everyone else Never.
Owner h receives zero under every unilateral replacement. Each observer's
joining gap is `delta_i({h})-R<0`; waiting receives its prescribed passive
reward. This is an exact absorbing terminal Nash profile, so

```text
A_(H_(-R)Z)(0)=0,        H_R(H_(-R)Z)=Z.            (14)
```

It follows that each of the following universal assertions is equivalent
to `A_abs(Z)=0` for EVERY own-zero Fin4 table:

- `A_Z(t)` is nondecreasing for t>=0, for every Z;
- `A_Z(t)` is nonincreasing for t>=0, for every Z.

For the first, combine monotonicity with (13). For the second, apply it
to the solved base `H_(-R)Z` and use (14). Conversely, if every native
absorbing gap vanishes, both monotonicity assertions are immediate.
The existing single-pivot normalization adapter identifies vanishing of
every such native gap as sufficient for the full quitting-game conjecture.
Accordingly, neither monotonicity direction can be imported as an
elementary deformation lemma: universally proving it would already solve
the missing global obligation.

The gap is nevertheless Lipschitz:

```text
|A_Z(t)-A_Z(s)|<=4|t-s|.                            (15)
```

For each row, the reward increments, including the unchanged Never
outcome, lie in an interval of length |t-s|. The cap increment and
prescribed-payoff increment lie in that interval, so each debt changes
by at most its length; take sums and infima. A hypothetical positive-gap
start therefore has a first zero at some finite T, with
`T>=A_Z(0)/4`. Nothing proved here prevents loss of the gap at that first
zero. Local openness does not carry the source across it.

The monotonicity equivalence was proposed by CODEX_QUADRANT_FINISH in
the focused transformation audit and independently checked here.

## 7. A singleton-only raise has a quantified gap-collapse channel

A third operation changes ONLY the original reward at the own singleton
of the carrying player h by lambda>=0, and then restores own-zero
normalization. Its native table is

```text
Z^lambda_h({h})=0,
Z^lambda_h(S)=Z_h(S)-lambda  for S!={h},
Z^lambda_i(S)=Z_i(S)         for i!=h.               (16)
```

Every nonempty joining contact is unchanged. Put
`u=1-e_h`, so the singleton matrix is
`Gamma_lambda=Gamma-lambda e_h u^T`. The determinant lemma and
Sherman--Morrison formula give, with `v=Gamma^(-1)e_h>0` and k as above,

```text
det Gamma_lambda = det Gamma (1-lambda k),
Gamma_lambda^(-1)e_h = v/(1-lambda k)
       for 0<=lambda<1/k.                         (17)
```

At `lambda_*=1/k` the matrix is singular, and beyond it the determinant
is negative. The already established native positive-gap necessity
therefore gives `A_abs(Z^lambda)=0` for every `lambda>=lambda_*`.
Precisely, a positive gap at such a native table would, after adding
one to every nonempty entry, give a positive unrestricted full gap by
properification and (6). The strict-column source theorem would then
require its unchanged singleton matrix to have positive determinant,
contradicting (17).

Before that boundary the same inverse-axis absorbing comparison gives

```text
A_abs(Z^lambda)
  <= c_h(1-lambda k),    c_h=v_h/(S k).             (18)
```

Indeed the new v, S and k are respectively the old quantities divided
by `1-lambda k`; substitution in the existing axis ceiling yields (18).
If the new gap is zero the bound is automatic; otherwise the same
native positive-gap source justifies every ingredient of that comparison.

The sharp row-oscillation estimate gives
`|A_abs(Z^lambda)-A|<=lambda`. Its guaranteed positivity range
`lambda<A` cannot reach the matrix boundary, because

```text
A<=c_h=(v_h/S)lambda_*<lambda_*.                   (19)
```

Positive row weighting does not repair this separation: the carrying
row's boundary becomes `a_h lambda_*`, while its axis competitor has
weighted debt at most `a_h c_h`. Thus the gap can collapse continuously
to zero along a source-specific route to a solved determinant boundary,
with the explicit upper envelope (18). No critical cap face is forced
before that collapse. This does not prove a positive gap exists, or
exclude every more sophisticated use of this homotopy; it identifies
the exact missing global preservation step.

## Source audit and remaining question

The source, complete tail, and scalar optimization are in
[CODEX_VARIATIONAL_ESCAPE__CONSTRAINED_REPAIR_AND_CONE_GRAFT_OBSTRUCTION](CODEX_VARIATIONAL_ESCAPE__CONSTRAINED_REPAIR_AND_CONE_GRAFT_OBSTRUCTION.md).
The critical-face proof is in
[CODEX_VARIATIONAL_ESCAPE__CONSTRAINED_PARTIAL_NASH_PREFIX_BARRIER](CODEX_VARIATIONAL_ESCAPE__CONSTRAINED_PARTIAL_NASH_PREFIX_BARRIER.md).
The new content here is the exact extended parameter range and the resulting
failure of the proposed penalty transition at `r=A`; the underlying tail and
critical-face theorems are reused unchanged.

Static declaration inspection was limited to
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
`UniformEquilibrium/Quitting/Root/CapNashRootStack.lean`,
`minimumTerminalSemantic_weightedAuxiliaryNash_criticalFace` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticWeightedAuxiliaryNashBudget.lean`,
and the positive semantic endpoint
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
None of these declarations is being represented as a Lean implementation of
this constrained penalty theorem. No Lean command was run.

A genuinely new next step must leave the row-affine orbit and the fixed-source
finite-prefix inertness argument. It must either produce a controlled
joint-cohort/whole-law comparison, or prove a source-specific global
preservation theorem for a deformation that changes native rewards.
The coordinatewise universal transport class in Section 5 cannot do this;
the monotonicity shortcut in Section 6 is equivalent to the original
obligation; and Section 7 supplies an explicit gap-collapse channel at
the natural singleton boundary. No new class exclusion or source-preserving
global deformation is proved here.
