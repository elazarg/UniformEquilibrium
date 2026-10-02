# A linked sibling inequality would convert barrier value into a renewal Lyapunov function

Author: CODEX_SPINOZA

## Status

**Exact conditional theorem and positive-floor abstract regression; not
Lean-checked and not a Fin4 consumer.** For a renewed alternating path, a
single scalar combination of the checked exact-block capacity potential
\(\Phi\) and the greatest target-free controller barrier \(Q\) rules out
infinite renewal under one linked-sibling inequality. The fixed phase-charge
floor and boundedness of \(Q\) automatically control how much \(Q\) can rise
along the vertical exact predecessor phase after choosing a sufficiently
small scalarization weight. The only genuine missing comparison prices the
horizontal capacity recharge by a decrease of \(Q\) across the literal
source-linked sibling cap update.

That horizontal comparison does not follow from the currently supplied
positive-minimum packet. The positive floor gives \(Q\ge\eta>0\), but the
required estimate concerns differences of \(Q\); adding a positive constant
changes neither.
An exact two-state abstract ledger with \(Q\equiv\eta\) realizes fixed
vertical charge and equal horizontal recharge indefinitely. It is not
claimed to be realizable by a quitting table.

## Question

What exact comparison between the common-tail sibling words

\[
 p_m=T_{v_m}z_m,
 \qquad
 s_{m+1}=T_{w_m}z_m
\tag{1}
\]

would turn the renewed cap-clock source into a contradiction to bounded
exact-block capacity?

## 1. Alternating data

Let \(s_m,p_m,s_{m+1}\) be decorated canonical boxed states. Assume:

1. \(s_m\to p_m\) is a finite exact Nash--Bellman predecessor path with
   charge \(A_m\ge0\);
2. \(p_m\dashrightarrow s_{m+1}\) is the actual one-player cap-child update;
3. \(\Phi\) is the bounded exact-block capacity-to-go potential, so

   \[
    \Phi(p_m)+A_m\le\Phi(s_m);
    \tag{2}
   \]

4. \(Q\) is the bounded greatest target-free universal-prefix barrier, so
   the solid prefix path gives

   \[
    Q(s_m)\le Q(p_m).
    \tag{3}
   \]

The actual cap child and its parent have the common-tail sibling
factorization (1) whenever the installed response is a deterministic finite
clock. This factorization gives

\[
 Q(z_m)\le Q(p_m),
 \qquad
 Q(z_m)\le Q(s_{m+1}),
\tag{4}
\]

but no ordering between the siblings.

Define

\[
 K_m=\Phi(s_{m+1})-\Phi(p_m),
 \qquad
 L_m=Q(s_{m+1})-Q(p_m).
\tag{5}
\]

The reviewed recharge ledger proves, under uniform positive phase charge,
that the \(K_m\) have positive linear cumulative growth. The bare barrier
ledger proves only a nonpositive upper Cesàro bound for the \(L_m\).

## 2. Exact combined-potential criterion

### Theorem 2.1

Assume one uniform phase-charge floor

\[
 A_m\ge a_0>0.
\tag{6}
\]

Since \(Q\) is bounded, choose \(B_Q\ge0\) such that

\[
 0\le Q(p_m)-Q(s_m)\le B_Q
\]

for every \(m\). Define

\[
\lambda=
\begin{cases}
 a_0/(2B_Q),&B_Q>0,\\
 1,&B_Q=0.
\end{cases}
\tag{7}
\]

Then the vertical leakage estimate is automatic:

\[
\lambda\bigl(Q(p_m)-Q(s_m)\bigr)\le A_m/2.
\tag{8}
\]

Suppose there are nonnegative errors \(\varepsilon_m\) with
\(\sum_m\varepsilon_m<\infty\) such that every horizontal seam satisfies the
single **linked sibling recharge bound**

\[
 \boxed{
 \Phi(s_{m+1})-\Phi(p_m)
 +\lambda\bigl(Q(s_{m+1})-Q(p_m)\bigr)\le\varepsilon_m.}
\tag{9}
\]

Then

\[
 \sum_m A_m<\infty.
\tag{10}
\]

This contradicts the floor (6). Hence no infinite renewed orbit can satisfy
(9).

#### Proof

Put

\[
 \Psi=\Phi+\lambda Q.
\tag{11}
\]

Across the solid phase, (2) and the automatic estimate (8) give

\[
\begin{aligned}
 \Psi(p_m)-\Psi(s_m)
 &=
 \Phi(p_m)-\Phi(s_m)
 +\lambda\bigl(Q(p_m)-Q(s_m)\bigr)\\
 &\le -A_m+A_m/2
 =-A_m/2.
\end{aligned}
\tag{12}
\]

Across the horizontal sibling seam, (9) gives

\[
\Psi(s_{m+1})-\Psi(p_m)\le\varepsilon_m.
\tag{13}
\]

Therefore

\[
 \Psi(s_{m+1})-\Psi(s_m)
\le-A_m/2+\varepsilon_m.
\tag{14}
\]

Both \(\Phi\) and \(Q\) are bounded on their compact state spaces, so
\(\Psi\) is bounded below. Summing (14) gives

\[
\frac12\sum_{m<N}A_m
\le \Psi(s_0)-\Psi(s_N)+\sum_{m<N}\varepsilon_m,
\]

which proves (10). QED

## 3. Meaning of the sibling inequality

Equation (9) is not merely \(Q(s_{m+1})\ge Q(p_m)\). It says that, up to the
summable error, any positive horizontal capacity recharge

\[
 K_m=\Phi(s_{m+1})-\Phi(p_m)>0
\]

must be paid by a quantitatively larger downward \(Q\)-move:

\[
 Q(p_m)-Q(s_{m+1})
 \ge \bigl(K_m-\varepsilon_m\bigr)/\lambda.
\tag{15}
\]

This is the exact cross-potential comparison needed to absorb the horizontal
seam. Weak \(Q\)-monotonicity in the opposite direction would force
\(K_m\le0\), which also closes renewal, but no such monotonicity is known for
nonstationary siblings.

No separate vertical theorem is needed. The uniform charge floor and the
global oscillation bound for \(Q\) make (8) automatic after shrinking
\(\lambda\). This is why the fixed-charge renewal packet is materially
stronger than a merely positive total charge with no per-phase floor.

Thus the horizontal linked-sibling estimate (9) is the only missing
inequality in this scalarization.

## 4. Audit against the positive-minimum source packet

Assume the hypothetical no-uniform-payoff branch. Then

\[
 Q(z)\ge\eta>0
\tag{16}
\]

for every carrier point. The structured cap-installation collar also gives

\[
 D(s_m)\ge D_*+\delta_{\mathrm{seg}}
\tag{17}
\]

on its source segment, while every exact first prefix spends fixed debt and
fixed absorption. These facts defeat the literal zero-gap all-Never boundary,
and the absorption floor supplies (6), hence the automatic vertical estimate
(8). They do not imply the horizontal inequality (9):

- (16) is a level bound, while (9) uses differences of \(Q\);
- (17) says the source is away from the total-debt minimum fibre, which
  permits rather than forbids a charged exact prefix;
- the fixed root debt drop controls \(D(s_m)-D(p_m)\), not the horizontal
  change of \(\Phi+\lambda Q\);
- the common-tail identity (1) gives the two inequalities in (4), not an
  ordering of the siblings; and
- cap attainment controls the mover's payoff and debt, while \(\Phi\) is a
  supremum of future exact Nash--Bellman charge and \(Q\) is an infimum of
  future arbitrary-prefix debt. Neither future value is determined by the
  one displayed response.

The one stationary source is better: a deterministic finite cap child is a
universal-prefix descendant of that stationary semantic point, so \(Q\)
cannot decrease on that single seam. But this provides no strict
charge-to-\(Q\) increment, and the resulting child is nonstationary. It
cannot supply (9) on later renewed seams.

## 5. Positive-floor abstract ledger regression

Fix numbers \(a>0\) and \(\eta>0\). Consider two abstract states \(S,P\) with

\[
 Q(S)=Q(P)=\eta,
\qquad
 \Phi(S)=a,\quad \Phi(P)=0.
\tag{18}
\]

Let the solid relation contain the charged edge

\[
 S\longrightarrow P,\qquad A=a,
\]

and let the horizontal update return

\[
 P\dashrightarrow S.
\]

Then:

- \(Q\) has the positive floor \(\eta\);
- it is nondecreasing on the solid edge, with zero increment;
- \(\Phi(P)+A=\Phi(S)\), so the vertical charge inequality is exact;
- the horizontal seam recharges exactly \(a\) units of \(\Phi\); and
- the cycle repeats forever.

The automatic vertical estimate (8) holds with zero left side, but the
linked sibling condition (9) fails by exactly \(a\) when
\(\varepsilon_m=0\).

This is an abstract regression to the **barrier-plus-capacity ledger
inference**, not a quitting-game counterexample. It shows why the positive
level \(\eta\) cannot replace a signed horizontal comparison: translating a
flat barrier from zero to \(\eta\) leaves every difference unchanged.

An actual Fin4 realization of (18) with \(\eta>0\) would itself be
counterexample-level information. No such realization is claimed or needed
for the algebraic boundary.

## 6. Exact falsifiable target

The source-specific remaining theorem can now be stated without ambiguity.
Use the fixed charge floor to choose \(\lambda\) by (7). For the linked
sibling words (1) produced by one renewed cap installation, seek summable
errors \(\varepsilon_m\) such that

\[
 \Phi(T_{w_m}z_m)-\Phi(T_{v_m}z_m)
 +\lambda\bigl(
 Q(T_{w_m}z_m)-Q(T_{v_m}z_m)
 \bigr)
 \le\varepsilon_m.
\tag{19}
\]

Theorem 2.1 would then consume every infinite fixed-charge renewal. A finite
quitting regression satisfying all renewed source fields but violating
(19) by a fixed amount would close this scalarization route negatively.

## Sources inspected

- formalized/QUITTING_CONTROLLER_TESTER_VALUE_AND_BARRIER_DUALITY.md;
- notes/CODEX_HAHN__RENEWED_OWNER_CYCLE_CAPACITY_RECHARGE_LEDGER.md,
  reviewed at SHA-256
  cd1a964b4c77073ade6a9ff371d294f1e3169a55883de39ea78320c9e21a54ef;
- notes/CODEX_SPINOZA__RENEWABLE_CAP_ORBIT_GLOBAL_BARRIER_NO_GO.md,
  twice reviewed at SHA-256
  cd8d489e2390ebfde21e5d061226dcec3a3d1e9c266e6096b36547d8cce46d2b;
- notes/CODEX_SPINOZA__FINITE_CAP_CHILD_BARRIER_ANCESTRY_AND_FLATNESS.md,
  frozen for review at SHA-256
  1e53b6b85cfa7d7fdaf2749418d8b9c713d6ec69498dd63c804c32dac86e99f6;
- notes/CODEX_HAHN__CAP_INSTALLATION_SEGMENT_COLLAR_AND_REACHED_TWO_CUT_BOUNDARY.md;
  and
- MathUE/ChargedPathBudget.lean, for the generic bounded
  capacity-to-go potential and its charged-edge decrement.

## Boundary and nonclaims

- Theorem 2.1 is a conditional algebraic consumer. It does not prove (9)
  from Fin4 data; the vertical estimate (8) is automatic.
- The abstract regression is not asserted to be a terminal semantic carrier,
  a quitting reward table, or a positive-gap counterexample.
- A positive global floor excludes the actual \(Q=0\) boundary tests, but
  does not exclude flat \(Q\) differences.
- The capacity potential and \(Q\) live on compatible decorated/semantic
  projections only after the source decorations are fixed as in the recharge
  ledger. Equation (9) is stated on those fixed decorations.
- No horizontal cap update is called an exact Nash--Bellman edge.

## Next exact question

Can the actual linked sibling cap update violate (19) by a fixed amount in a
finite two-sure-clock quitting table while retaining the cap-pin collar, or
does the source-linked exact root structure impose a hidden comparison
between future exact-block capacity and future arbitrary-prefix debt?
