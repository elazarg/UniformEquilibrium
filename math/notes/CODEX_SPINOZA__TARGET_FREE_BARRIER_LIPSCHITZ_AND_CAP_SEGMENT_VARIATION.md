# The target-free barrier is Lipschitz, but cap-segment variation is unsigned

Author: CODEX_SPINOZA

## Status

**Exact ordinary mathematics with a checked nonexpansive-prefix input; not
Lean-checked as a combined theorem and not a consumer.** The greatest
target-free universal-prefix barrier \(Q\) is globally \(2\)-Lipschitz in the
coordinatewise sup norm on terminal semantic pairs. If two actual profiles
differ only in one player's stopping law by total variation \(\delta\), their
semantic pairs are within \(2M\delta\), uniformly over all unrestricted
behavioral cap coordinates. Hence their \(Q\)-values differ by at most
\(4M\delta\).

Along a private cap-installation segment, \(Q\) has bounded variation at most
\(4M\) and its final slice has variation proportional to the slice width.
At the cap-pinned proper point used by the exact-root expenditure theorem,
this variation is bounded by an explicit constant times the root absorption
floor. The estimate is unsigned and does not control the canonical
exact-block capacity potential across the horizontal seam. It therefore does
not supply the linked-sibling Lyapunov inequality.

## Question

Can the common-tail sibling factorization and the semantic metric turn the
horizontal cap installation into a charge-relative \(Q\)-estimate strong
enough to control capacity recharge?

## 1. Semantic metric and prefix nonexpansiveness

For terminal semantic pairs \(p=(u,B)\) and \(q=(v,C)\), define

\[
 \rho(p,q)=
 \max\left\{
 \max_i|u_i-v_i|,
 \max_i|B_i-C_i|
 \right\}.
\tag{1}
\]

The checked theorem quittingTerminalSemanticPrefix_within says that every
fixed product-root prefix \(T_x\) is nonexpansive:

\[
 \rho(T_xp,T_xq)\le\rho(p,q).
\tag{2}
\]

Iteration gives the same estimate for every finite arbitrary-root word \(w\):

\[
 \rho(T_wp,T_wq)\le\rho(p,q).
\tag{3}
\]

Let

\[
 d(u,B)=\max_i(B_i-u_i).
\tag{4}
\]

For every \(i\),

\[
 |(B_i-u_i)-(C_i-v_i)|
 \le |B_i-C_i|+|u_i-v_i|
 \le2\rho(p,q),
\]

and taking maxima gives

\[
 |d(p)-d(q)|\le2\rho(p,q).
\tag{5}
\]

## 2. Global barrier Lipschitz theorem

Define the target-free universal-prefix envelope

\[
 Q(p)=\inf_w d(T_wp),
\tag{6}
\]

where \(w\) ranges over all finite words of independent product roots,
including the empty word.

### Theorem 2.1

For all semantic pairs \(p,q\) in the bounded semantic box,

\[
 \boxed{|Q(p)-Q(q)|\le2\rho(p,q).}
\tag{7}
\]

#### Proof

Equations (3) and (5) give, uniformly in \(w\),

\[
 |d(T_wp)-d(T_wq)|\le2\rho(p,q).
\tag{8}
\]

Therefore

\[
 d(T_wp)\le d(T_wq)+2\rho(p,q)
\]

for every word. Taking infima yields

\[
 Q(p)\le Q(q)+2\rho(p,q).
\]

Interchanging \(p,q\) proves (7). QED

Thus the greatest barrier is in fact continuous and Lipschitz, stronger than
the upper semicontinuity obtained formally by viewing it as an arbitrary
infimum of continuous finite-word objectives. The improvement comes from the
uniform nonexpansive constant over all word lengths.

## 3. One-player stopping-law stability

Assume all terminal rewards, including the nonabsorption payoff zero, lie in
\([-M,M]\). Let \(\sigma,\tau\) be actual profiles with identical opponents
of one player \(k\), and let their prescribed \(k\)-stopping laws have total
variation distance at most \(\delta\).

### Proposition 3.1

\[
 \boxed{
 \rho(\operatorname{Sem}(\sigma),\operatorname{Sem}(\tau))
 \le2M\delta.}
\tag{9}
\]

Consequently

\[
 \boxed{
 |Q(\operatorname{Sem}(\sigma))
   -Q(\operatorname{Sem}(\tau))|
 \le4M\delta.}
\tag{10}
\]

#### Proof

Couple the two \(k\)-stopping times so that they disagree with probability at
most \(\delta\), and use identical opponent randomness. The terminal outcome
and every coordinate payoff agree unless the coupled \(k\)-times disagree.
Each payoff changes by at most \(2M\), proving the prescribed-payoff half of
(9).

Player \(k\)'s cap is unchanged because its opponents are identical. For an
outsider \(i\ne k\), fix an arbitrary behavioral deviation of \(i\) and use
the same deviation randomness in the coupling. The only changed opponent law
is still \(k\)'s, so the two deviation payoffs differ by at most
\(2M\delta\), uniformly over the complete behavioral strategy class.
Taking suprema preserves this bound:

\[
 |\sup_\beta f_\sigma(\beta)-\sup_\beta f_\tau(\beta)|
 \le\sup_\beta|f_\sigma(\beta)-f_\tau(\beta)|
 \le2M\delta.
\]

This proves the cap half of (9). Equation (10) follows from Theorem 2.1.
QED

The argument covers arbitrary randomized, calendar-dependent, and Never
deviations. It does not rely on cap attainment.

## 4. Cap-installation segment

Let \(A_k\) be an actual complete cap-attaining response for \(k\) at
\(\sigma\). For \(t\in[0,1]\), replace \(k\)'s stopping law by

\[
 \mu_t=(1-t)\operatorname{Law}(\sigma_k)
       +t\operatorname{Law}(A_k)
\tag{11}
\]

and call the resulting profile \(\sigma^t\). Put
\(X^t=\operatorname{Sem}(\sigma^t)\). For \(s,t\in[0,1]\),

\[
 \|\mu_t-\mu_s\|_{\mathrm{TV}}
 =|t-s|\,
 \|\operatorname{Law}(A_k)-\operatorname{Law}(\sigma_k)\|_{\mathrm{TV}}
 \le|t-s|.
\tag{12}
\]

Proposition 3.1 gives

\[
 \rho(X^t,X^s)\le2M|t-s|
\tag{13}
\]

and

\[
 \boxed{|Q(X^t)-Q(X^s)|\le4M|t-s|.}
\tag{14}
\]

For every partition \(0=t_0<\cdots<t_N=1\),

\[
 \sum_{\ell<N}
 |Q(X^{t_{\ell+1}})-Q(X^{t_\ell})|
 \le4M.
\tag{15}
\]

Thus \(Q\) has total variation at most \(4M\) along one full cap-installation
segment. This is stronger than a pointwise continuity statement and is
uniform over the chosen cap response.

## 5. Comparison with the exact-root absorption scale

Return to the structured source with

\[
 d_k(X^0)\ge\gamma>0,
\qquad
 B_k(X^0)\to r_k(\{k\})
\]

along the source sequence. Fix \(0<\lambda<1\) and use the proper segment
point

\[
 t_*=1-\lambda.
\]

The owner debt at \(X^{t_*}\) is at least

\[
 g=\lambda\gamma.
\]

For every sufficiently late source, the fixed-cap-pin theorem gives every
exact payoff-tail root at \(X^{t_*}\) the absorption floor

\[
 a_0=\min\{1,g/(16M)\}.
\tag{16}
\]

Since every unilateral gain is at most \(2M\), one has
\(\gamma\le2M\). Hence \(g/(16M)<1\) and

\[
 a_0=\frac{\lambda\gamma}{16M}.
\tag{17}
\]

The final cap slice has

\[
 \|\mu_1-\mu_{t_*}\|_{\mathrm{TV}}
 \le\lambda,
\]

so (10) yields

\[
\boxed{
 |Q(X^1)-Q(X^{t_*})|
 \le4M\lambda
 =\frac{64M^2}{\gamma}\,a_0.}
\tag{18}
\]

Thus the source-level \(Q\)-variation is quantitatively of at most the same
order as the root absorption floor. This is the strongest direct
charge-relative estimate obtained from the cap-segment parameter.

## 6. Combination with the two-sure universal-descendant theorem

Suppose the renewed branch has reached the stage where every horizontal cap
child retains two distinct prescribed finite sure-clock players.  The
two-sure descendant theorem then gives, for the alternating phase

\[
 s_m\longrightarrow p_m\dashrightarrow s_{m+1},
\]

literal finite words \(v_m,w_m\) with

\[
 p_m=T_{v_m}s_m,
 \qquad
 s_{m+1}=T_{w_m}p_m.
\tag{19}
\]

Consequently

\[
 0\le L_m:=Q(s_{m+1})-Q(p_m),
\tag{20}
\]

and boundedness of \(Q\), together with the same monotonicity on the vertical
word, gives

\[
 \sum_m L_m<\infty.
\tag{21}
\]

If the horizontal child changes one player's stopping law by total variation
\(\delta_m\), Proposition 3.1 adds the quantitative upper bound

\[
\boxed{0\le L_m\le4M\delta_m.}
\tag{22}
\]

This is the favorable sign for the alternative potential
\(\tilde\Psi=\Phi-\lambda Q\).  It still has the wrong modulus for
capacity recharge.  To pay a positive recharge

\[
 K_m=\Phi(s_{m+1})-\Phi(p_m)
\]

by (20), one needs an estimate of the form

\[
K_m\le\lambda L_m+\varepsilon_m,
\tag{23}
\]

not the upper estimate \(L_m\le4M\delta_m\).  In particular, (21) does not
imply that the semantic distance or the stopping-law distance is summable:
a Lipschitz function can be flat on a macroscopic fibre.

This direction issue is exact.  The positive floor \(Q\ge\eta\) controls the
level of the scalar function, not an inverse modulus for its fibres.  A
lower estimate

\[
c\,\rho(p_m,s_{m+1})\le L_m
\tag{24}
\]

would be a new source-specific separation theorem; it is not a consequence
of Lipschitz continuity, the two-sure descendant identity, or the
off-minimum total-debt collar.

## 7. Why the estimate does not close the seam

Equation (18) has three exact limitations.

1. **No sign at the source slice.** It permits \(Q\) to rise, fall, or remain
   flat across the raw cap-installation segment. On the later two-sure
   descendant seam the sign is favorable for \(\Phi-\lambda Q\), but (22)
   remains only an upper bound and gives no capacity-pricing modulus.
2. **Wrong potential.** It bounds only \(Q\). The canonical capacity
   potential \(\Phi\) is a supremum over future exact Nash--Bellman paths.
   No continuity or Lipschitz theorem bounds
   \(\Phi(\text{cap child})-\Phi(\text{parent})\) by semantic distance.
3. **Source versus post-prefix seam.** Equation (18) compares two points on
   the private source cap segment. After inserting an exact root, the later
   transported cap update is a linked sibling over a shifted tail. It is not
   automatically the same pair \(X^{t_*},X^1\).

Subdividing one installation does not repair the sign: (15) controls the
total absolute \(Q\)-variation of that one segment, but an infinite renewed
orbit contains one macroscopic installation per phase. The resulting bound
is linear, not summable.

The positive global floor \(Q\ge\eta>0\) prevents the barrier from reaching
zero, but it does not orient (18). The cap-segment debt collar similarly
keeps every segment point off the total-debt minimum fibre without choosing
a sign for \(Q\).

## Sources inspected

- UniformEquilibrium/Quitting/Root/TerminalSemanticPrefixMetric.lean,
  especially quittingTerminalSemanticPrefix_within and its root-dependent
  contraction refinement;
- formalized/QUITTING_CONTROLLER_TESTER_VALUE_AND_BARRIER_DUALITY.md;
- UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean;
- UniformEquilibrium/Quitting/Paths/StoppingLawMixture.lean;
- notes/CODEX_HAHN__CAP_INSTALLATION_SEGMENT_COLLAR_AND_REACHED_TWO_CUT_BOUNDARY.md,
  reviewed after repair at SHA-256
  f69b6f7b167d81789add1e48e77220ad6418d7cff3715169b276649063f51be5;
- notes/CODEX_SPINOZA__FINITE_CAP_CHILD_BARRIER_ANCESTRY_AND_FLATNESS.md,
  frozen at SHA-256
  1e53b6b85cfa7d7fdaf2749418d8b9c713d6ec69498dd63c804c32dac86e99f6;
- notes/CODEX_HAHN__TWO_SURE_CLOCK_CHILD_IS_UNIVERSAL_PREFIX_DESCENDANT.md,
  reviewed at SHA-256
  8296721fcfad9e373c012b01481ae414ef0f7c0cda86f7a1868a46ec563f82ad;
  and
- notes/CODEX_SPINOZA__LINKED_SIBLING_BARRIER_CAPACITY_LYAPUNOV_CRITERION.md.

## Boundary and nonclaims

- Total variation uses \(\sup_A|\mu(A)-\nu(A)|\); the payoff constant is
  \(2M\delta\), not \(M\delta\).
- The semantic cap estimate is uniform over unrestricted behavioral
  deviations because the coupling bound is uniform before taking the
  supremum.
- The theorem establishes continuity of \(Q\), not of the capacity potential
  \(\Phi\).
- The cap gain gives a lower bound on the endpoint law displacement, whereas
  (10) uses an upper bound. These directions cannot be interchanged.
- Equation (18) is an unsigned magnitude estimate, not a chronological
  charge or a source-reprojected return.
- On the two-sure branch the horizontal \(Q\)-increment is nonnegative and
  summable, but the Lipschitz theorem bounds it from above by semantic
  displacement.  It supplies neither the inverse estimate (24) nor the
  capacity comparison (23).

## Next exact question

On the positive-minimum two-sure cap-child family, can one prove either the
inverse barrier separation (24) or the direct capacity comparison (23)?  A
proof must use source-specific exact-root structure: global Lipschitz
regularity gives precisely the opposite inequality.
