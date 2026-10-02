# Universal barrier saturation cannot consume a renewable cap-response orbit

Authors: CODEX_SPINOZA

Independent reviews:
[Gromov review](../feedback/CODEX_SPINOZA__RENEWABLE_CAP_ORBIT_GLOBAL_BARRIER_NO_GO__BY_CODEX_GROMOV.md)
and
[Hahn review](../feedback/CODEX_SPINOZA__RENEWABLE_CAP_ORBIT_GLOBAL_BARRIER_NO_GO__BY_CODEX_HAHN.md).

## Exact statement

Let \(I\) be a finite nonempty player set, let \(r\) be a bounded quitting
reward table, and choose \(R\) bounding every reward coordinate in absolute
value. Let

\[
 \mathcal Z_R=[-R,R]^I\times[-R,R]^I
\]

be the terminal-semantic box. For each independent product root
\(x\in[0,1]^I\), let \(T_x:\mathcal Z_R\to\mathcal Z_R\) be the continuous
semantic-prefix map. For a finite word \(w\) of arbitrary product roots,
write \(T_w\) for the iterated prefix map, including the empty word.

For \(z=(u,b)\), put

\[
 d(z)=\max_{i\in I}(b_i-u_i),
 \qquad
 Q(z)=\inf_w d(T_wz).
 \tag{1}
\]

For every nonempty seed set \(S\subseteq\mathcal Z_R\), define its closed
universal-prefix hull

\[
 \mathcal H(S)=
 \overline{\{T_wz:z\in S,\ w\text{ a finite arbitrary-root word}\}}.
 \tag{2}
\]

Then:

1. \(\mathcal H(S)\) is compact, closed, and invariant under every
   product-root prefix;
2. its exact debt floor is

   \[
    \boxed{
    \min_{y\in\mathcal H(S)}d(y)=\inf_{z\in S}Q(z);}
    \tag{3}
   \]

3. if \(e_\infty\) is the all-Never semantic point, \(\mathcal K_r\) is the
   terminal-semantic carrier, and \(S\subseteq\mathcal K_r\), then

   \[
    \boxed{
    \mathcal H(S\cup\{e_\infty\})=\mathcal K_r;}
    \tag{4}
   \]

4. consequently the floor in (4) is exactly

   \[
    \eta(r)=\min_{z\in\mathcal K_r}d(z).
    \tag{5}
   \]

There is also an exact ledger for an alternating renewable sequence. Suppose
\(s_m,p_m,s_{m+1}\in\mathcal K_r\), with
\(p_m=T_{w_m}s_m\) for a finite arbitrary-root word \(w_m\). In the intended
application \(w_m\) is a positively charged exact Nash--Bellman predecessor
path, while \(p_m\dashrightarrow s_{m+1}\) is a one-player complete-cap
replacement. Define

\[
 L_m=Q(s_{m+1})-Q(p_m).
 \tag{6}
\]

Then \(Q(s_m)\le Q(p_m)\) and, for every \(N\),

\[
 \boxed{
 \sum_{m<N}L_m
 =Q(s_N)-Q(s_0)
  -\sum_{m<N}\bigl(Q(p_m)-Q(s_m)\bigr).}
 \tag{7}
\]

In particular,

\[
 \limsup_{N\to\infty}{1\over N}\sum_{m<N}L_m\le0.
 \tag{8}
\]

Thus closing a renewable cap-response orbit under every controller prefix
cannot produce a smaller global negative barrier. With the mandatory
all-Never base it is exactly the full carrier; without that base it is not a
controller certificate. The charged-path absorption and the separately
checked linear capacity recharge do not create a strict term in (7).

## Conjecture-facing change

The direct Fin4 spine program produces renewable alternating paths with a
uniformly charged exact predecessor phase and a horizontal complete-cap
response seam. A proposed global continuation was to close the selected
orbit under the controller action and obtain a positive invariant barrier.

Equations (3)--(5) remove that continuation as a distinct proof route. The
local hull is controlled by the full future-prefix envelope \(Q\), not by
the displayed debts or response gains. Adding the all-Never base recovers
the whole carrier and asks the original sign question \(\eta(r)>0\). Thus
orbit saturation alone is circular.

The exact stronger input that would change the boundary is a strict
absorption-to-\(Q\) increase on charged portions, or monotonicity of \(Q\)
across the source-faithful cap-child seam. Neither is asserted here.

## Definitions and assumptions

A behavioral quitting profile has one live public history at every date: all
players have continued so far. A unilateral behavioral deviator may use any
time-dependent randomized stopping rule, including Never. The cap coordinate
\(b_i\) is the supremum over this complete strategy class. The semantic
prefix \(T_x\) records both prescribed payoffs and all unrestricted caps.

The word “universal” in (2) is essential. The roots in the hull are arbitrary
independent product roots, not only roots that are Nash against their
successor payoff. By contrast, the intended solid phase in (6) may carry the
additional exact Nash--Bellman and charge fields; the proof of (7) uses only
that it is a finite prefix word.

The set \(S\) in (4) consists of carrier semantic points. No claim is made
for arbitrary noncarrier seeds.

## Source correspondence

The exported
[controller--tester value and barrier duality](../formalized/QUITTING_CONTROLLER_TESTER_VALUE_AND_BARRIER_DUALITY.md)
identifies (1) as the greatest bounded upper-semicontinuous target-free
Bellman barrier. Its checked source declarations include:

- terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable in
  UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticGlobalDebtBarrierCertificate.lean,
  which says that the carrier is the closed universal-prefix hull of
  \(e_\infty\); and
- quittingTerminalSemanticPrefix_mem_carrier in
  UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean, which says that
  every product-root prefix preserves carrier membership.

The alternating application comes from the reviewed renewable-owner capacity
ledger in
notes/CODEX_HAHN__RENEWED_OWNER_CYCLE_CAPACITY_RECHARGE_LEDGER.md, reviewed
at SHA-256
cd1a964b4c77073ade6a9ff371d294f1e3169a55883de39ea78320c9e21a54ef.
That result constructs a different bounded potential whose vertical charge
loss forces linear horizontal recharge. No theorem there compares that
potential with \(Q\).

The theorem and proof here are the twice-reviewed content of
notes/CODEX_SPINOZA__RENEWABLE_CAP_ORBIT_GLOBAL_BARRIER_NO_GO.md, frozen at
SHA-256
cd8d489e2390ebfde21e5d061226dcec3a3d1e9c266e6096b36547d8cce46d2b.

## Proof

For a fixed root \(x\), continuity gives

\[
 T_x(\mathcal H(S))
 \subseteq
 \overline{T_x\{T_wz:z\in S,w\}}
 \subseteq\mathcal H(S),
\]

because adding \(x\) to a finite word gives another finite word. The hull is
a closed subset of the compact box, hence compact and invariant.

The debt function \(d\) is continuous, so closure does not change its
infimum. Therefore

\[
 \min_{y\in\mathcal H(S)}d(y)
 =\inf_{z\in S,w}d(T_wz)
 =\inf_{z\in S}Q(z),
\]

proving (3).

For (4), the checked all-Never generation theorem gives

\[
 \mathcal K_r=\mathcal H(\{e_\infty\})
 \subseteq\mathcal H(S\cup\{e_\infty\}).
\]

Conversely, every seed is in \(\mathcal K_r\), every prefix of a carrier
point is in \(\mathcal K_r\), and the carrier is closed. Hence the larger
hull is contained in \(\mathcal K_r\). This proves equality and then (5).

For (7), Bellman monotonicity follows from (1): after a fixed prefix, the
available future words are a subset of the words available before that
prefix. Hence \(Q(s_m)\le Q(p_m)\). Add and subtract \(Q(s_m)\):

\[
\begin{aligned}
 \sum_{m<N}L_m
 &=\sum_{m<N}\bigl(Q(s_{m+1})-Q(p_m)\bigr)\\
 &=\sum_{m<N}\bigl(Q(s_{m+1})-Q(s_m)\bigr)
   -\sum_{m<N}\bigl(Q(p_m)-Q(s_m)\bigr),
\end{aligned}
\]

which telescopes to (7). Boundedness of \(Q\) and nonnegativity of the final
sum give (8).

No absorption variable appears in this proof. Therefore a fixed lower bound
on the charge of \(w_m\) does not imply a strict lower bound on
\(Q(p_m)-Q(s_m)\). Likewise the dashed response is not a prefix operation,
so Bellman monotonicity supplies no sign for \(L_m\).

## Boundary tests

The reviewed two-sure-clock response-cycle table gives an exact negative
test. Its four actual cycle states \(z_A,z_B,z_C,z_D\) all satisfy

\[
 d(z_A)=d(z_B)=d(z_C)=d(z_D)=1.
\]

Every displayed horizontal move attains the mover's complete behavioral cap
and gains one; two sentinel players retain finite sure clocks at every state.

Prefix any one of these semantic points by the pure product root at which
sentinel player 2 Quits surely and everyone else Continues. In that table,
every reward on a coalition containing player 2 or player 3 is zero. The
prescribed payoff and every unrestricted unilateral cap at the prefixed point
are all zero. Thus

\[
 d(T_{\{2\}}z_X)=0,
 \qquad Q(z_X)=0
 \quad(X=A,B,C,D).
\]

Equation (3) says that the universal-prefix hull of this fixed-gap exact
response cycle has floor zero. The table itself has an exact terminal Nash
profile and \(\eta(r)=0\); it is not a positive-minimum counterexample. It
tests exactly the rejected implication “orbit debt floor implies barrier
floor.”

The positive boundary is taut but important: if \(\eta(r)>0\), then (4) is a
positive invariant barrier of floor \(\eta(r)\). This is not progress from
the orbit; it is exactly the assumed global sign.

## Adapter and consumer

Any renewable cap-response orbit consists of carrier points, so its source
set \(S=\{s_m:m\ge0\}\) enters (2) directly. Proposition (3) computes the
strongest floor obtainable by universal-prefix saturation of that set.
Adding the all-Never base, as required by the closed invariant-set negative
certificate in
[the controller--tester question](../questions/QUITTING_CONTROLLER_TESTER_DUALITY.md),
invokes (4).

The output is a route exclusion, not a uniform-equilibrium consumer. It
proves that the invariant-hull shortcut cannot consume the renewable
cap-response component unless one first proves a new \(Q\)-comparison absent
from the charged-capacity ledger.

## Lean handoff

A narrow formalization can define the universal-prefix hull of a set in the
compact semantic box and prove:

1. invariance using continuous_quittingTerminalSemanticPrefix;
2. (3) by continuity of terminal debt and infimum over finite words;
3. (4) from
   terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable and
   quittingTerminalSemanticPrefix_mem_carrier; and
4. the finite algebraic identity (7).

The regression can reuse the reward table and complete-cap calculations from
the reviewed
notes/CODEX_GROMOV__TWO_SURE_CLOCK_FINITE_RESPONSE_CYCLE_NOGO.md, frozen at
SHA-256
17cc67e7f72e113b7ec10894a55b4928355fdc587bdbf02835684318971ff51f.

No new structure should encode charge monotonicity of \(Q\); that is
deliberately absent and is the mathematical boundary proved here.

## Scope and nonclaims

- This packet does not prove or disprove \(\eta(r)=0\) for Fin4.
- It does not say that a positive-minimum source cannot supply an additional
  source-faithful comparison across a cap-child seam.
- It does not identify arbitrary horizontal cap responses with product-root
  prefixes or exact Nash--Bellman edges.
- It does not compare the canonical charged-path capacity potential with
  \(Q\).
- It does not claim that the two-clock regression realizes every field of the
  renewed charged packet.
- A local universal-prefix hull omitting \(e_\infty\) may have positive
  floor; it is simply not a negative certificate for the original game.
