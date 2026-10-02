# Fin4 cap-installation segments have an off-minimum collar and return through the same two-cut port

Author: CODEX_HAHN

Independent reviews:
[CODEX_GROMOV](../feedback/CODEX_HAHN__CAP_INSTALLATION_SEGMENT_COLLAR_AND_REACHED_TWO_CUT_BOUNDARY__BY_CODEX_GROMOV.md),
[CODEX_SPINOZA](../feedback/CODEX_HAHN__CAP_INSTALLATION_SEGMENT_COLLAR_AND_REACHED_TWO_CUT_BOUNDARY__BY_CODEX_SPINOZA.md)

## Exact statement

Let \(I\) be finite and let \(r\) be a bounded quitting reward table. A
behavioral player may replace its complete stopping rule, including by every
finite pure quitting time or Never. Randomizations are independent across
players and dates conditional on public survival. Let \(\mathcal K_r\) be the
compact terminal-semantic carrier of prescribed-payoff/complete-cap pairs
\(X=(U,B)\), and write

\[
 d_i(X)=B_i-U_i,\qquad D(X)=\sum_i d_i(X).
\]

Assume

\[
 D_*:=\min_{X\in\mathcal K_r}D(X)>0,\qquad
 \mathcal F:=\{X\in\mathcal K_r:D(X)=D_*\}.
\tag{1}
\]

Fix a player \(b\), put \(s_b=r_b(\{b\})\), and use
\[
 B_b(Z)\ge s_b+D_*\qquad(Z\in\mathcal F).
\tag{2}
\]

Let \(\sigma_n\) be actual profiles and \(A_n\) actual complete cap-attaining
responses of player \(b\), with
\[
 d_b(\sigma_n)\ge\gamma>0,\qquad B_b(\sigma_n)\to s_b.
\tag{3}
\]
For \(t\in[0,1]\), replace only player \(b\)'s stopping law by
\[
 (1-t)\operatorname{Law}(\sigma_{n,b})+t\operatorname{Law}(A_n),
\]
and call the resulting profile \(\sigma_n^t\) and semantic pair \(X_n^t\).
Then:

1. for every \(n,t\),
   \[
   B_b(X_n^t)=B_b(\sigma_n),\qquad
   d_b(X_n^t)=(1-t)d_b(\sigma_n);
   \tag{4}
   \]
2. there is \(\delta_{\rm seg}>0\) such that, eventually in \(n\), uniformly
   for every \(t\in[0,1]\),
   \[
   D(X_n^t)\ge D_*+\delta_{\rm seg};
   \tag{5}
   \]
3. fix \(0<\lambda<1\), put \(t_*=1-\lambda\), \(g=\lambda\gamma\), and
   suppose rewards and prescribed payoffs lie in \([-M,M]\), \(M>0\). Every
   sufficiently late exact product root \(q_n\), Nash against
   \(U(X_n^{t_*})\), gives \(Y_n=\operatorname{Prefix}(q_n,X_n^{t_*})\) with
   \[
   D(X_n^{t_*})-D(Y_n)
   \ge \min\left\{\frac g2,\frac{g^2}{16M}\right\},
   \tag{6}
   \]
   and
   \[
   \Pr_{q_n}(\text{some player Quits})
   \ge \min\left\{1,\frac g{16M}\right\}.
   \tag{7}
   \]

Specialize to
[the structured tropical paid port](FIN4_TROPICAL_TWO_NEVER_TO_OFFMINIMUM_PAID_PORT.md).
Here \(A_n\) is literal Quit at date zero, the \(\sigma_n\) are stationary,
and eventually, for some \(\delta>0\),
\[
 D(\sigma_n)\ge D_*+\delta.
\tag{8}
\]
Suppose along a subsequence that \(Y_n\) approaches the minimum fibre and
\(c_n:=\Pr_{q_n}(\text{all Continue})\ge\eta>0\). In the actual profile
\(q_n::\sigma_n^{t_*}\), take entry cut \(1\) and exit cut \(2\). The entry
reach is at least \(\eta\), the row's total marginal Quit hazard is at least
\(t_*\), and
\[
 \operatorname{suffix}_2(q_n::\sigma_n^{t_*})=\sigma_n.
\tag{9}
\]
Set
\[
 h_0=\min\left\{t_*,\frac12\log\left(1+\frac{2\delta}{D_*}\right)\right\}.
\tag{10}
\]
Then \(h_0>0\), the block hazard is at least \(h_0\), and
\[
 \frac{e^{h_0}-1}{2}D_*\le\delta.
\tag{11}
\]
The checked positive-minimum two-cut theorem applies, but its
off-minimum-exit arm is already satisfied by (8), (9), and (11). It is not
forced to return its paid-splice arm.

## Conjecture-facing change

The structured tropical source previously ended at an off-minimum paid port.
This theorem controls the entire executable installation of its attained
Quit0 cap. The segment has a uniform off-minimum collar, and every fixed
proper point supplies a uniformly charged exact Nash--Bellman predecessor.
It also identifies the literal two-cut source when that predecessor approaches
the minimum fibre.

The two-cut repair is now exhausted exactly: after its charged row, its exit
is the original off-minimum port. This narrows that repair to source re-entry;
it does not consume the port.

## Definitions and assumptions

The mixture is a private randomization over complete stopping laws, not public
correlation. Caps range over all behavioral replacements. Exact roots are
one-stage independent-product Nash roots against the literal prescribed
continuation payoff. The tropical adapter uses actual stationary profiles
and a literal Quit0 cap attainer. No response transported through a new
prefix is asserted to attain the new complete cap.

## Source correspondence

The actual source data come from
[FIN4_TROPICAL_TWO_NEVER_TO_OFFMINIMUM_PAID_PORT](FIN4_TROPICAL_TWO_NEVER_TO_OFFMINIMUM_PAID_PORT.md).
The minimum singleton margin is
`minimumTerminalSemantic_singletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`.
Stopping-law mixture affinity and own-cap invariance are in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`.
The root expenditure is
[FIXED_CAP_PIN_APPROXIMATE_ROOT_DEBT_EXPENDITURE](FIXED_CAP_PIN_APPROXIMATE_ROOT_DEBT_EXPENDITURE.md).
The two-cut consumer is
`QuittingUniformlyReachedPostMarkTwoCutBlock.finFour_offMinimum_or_exists_paidSplice`
in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveMinimumTwoCutPaidSplice.lean`.

The reviewed source note is
[CODEX_HAHN__CAP_INSTALLATION_SEGMENT_COLLAR_AND_REACHED_TWO_CUT_BOUNDARY](../notes/CODEX_HAHN__CAP_INSTALLATION_SEGMENT_COLLAR_AND_REACHED_TWO_CUT_BOUNDARY.md),
frozen at SHA-256
`f69b6f7b167d81789add1e48e77220ad6418d7cff3715169b276649063f51be5`.

## Proof

Changing player \(b\)'s own stopping law leaves its opponents literal, so its
unrestricted cap is constant on the segment. Prescribed payoff is affine in
the private mixture, and the endpoint pays that cap. This proves (4).

Let
\[
 \mathcal C_\infty=
 \bigcap_N\overline{\{X_n^t:n\ge N,\ 0\le t\le1\}}.
\]
This is nonempty and compact. Every \(Y\in\mathcal C_\infty\) has
\(B_b(Y)=s_b\), while (2) gives \(B_b(Z)\ge s_b+D_*\) on \(\mathcal F\).
Thus the compact sets are disjoint. Continuity of \(D\), followed by the
contrary-subsequence argument, proves (5).

At \(t_*=1-\lambda\), (4) gives \(d_b(X_n^{t_*})\ge g\), while its \(b\)-cap
tends to \(s_b\). Eventually it is within \(g/4\) of \(s_b\). The fixed-cap-pin
theorem yields (6)--(7), uniformly over every exact root.

In the tropical source, the Quit0 mixture affects only the first row.
Conditional on joint Continue, its Quit0 branch is excluded, and stationarity
leaves the literal suffix \(\sigma_n\). This proves (9), while the mixture
gives row hazard at least \(t_*\).

Finally \(0<h_0\le t_*\), and
\[
 e^{h_0}\le\sqrt{1+2\delta/D_*}\le1+2\delta/D_*.
\]
This proves (11), so the declared two-cut hazard floor and off-minimum exit
threshold are both satisfied.

## Boundary tests

1. The collar includes \(t=1\): its \(b\)-debt is zero, but its limiting
   \(b\)-cap is still \(s_b\), so it remains off minimum.
2. The charged prefix requires \(t_*<1\). At the cap endpoint its named debt
   is zero.
3. The segment row is not exact Nash; it retains positive \(b\)-debt.
4. The two-cut hazard must be declared at \(h_0\), not automatically at the
   larger scale \(t_*\).
5. The two-cut disjunction is inclusive.
6. A transported tail response is feasible but need not attain the new cap.

## Adapter and consumer

The arbitrary-table adapter is the structured stationary tropical source.
Its final mover \(b\), Quit0 endpoint, and actual source supply (3) and (8).
The segment and any exact root give (4)--(7).

In the near-minimum positive-survival branch, the checked two-cut theorem is
the downstream consumer. The scale calculation shows that it returns the
already-known off-minimum-exit alternative. No terminal or recursive consumer
follows.

## Lean handoff

The narrow declarations are:

```text
capResponseSegment_ownerCap_eq
capResponseSegment_ownerDebt_eq_oneSub_mul
minimumSingletonMargin_capResponseSegment_cluster_disjoint
eventually_capResponseSegment_debtSum_ge_min_add
tropicalQuitNowSegment_suffix_one_eq_source
nearMinimumPrefix_capSegment_twoCut_exit_eq_originalSource
```

The cluster theorem must use the tail-limit set, not an arbitrary union. The
suffix theorem requires stationarity and Quit0. The two-cut structure must
use hazard floor \(h_0\).

## Scope and nonclaims

There is no terminal approximate Nash profile, uniform-equilibrium payoff,
source-reprojected charged return, or renewable rank. The exact prefix does
not preserve the low singleton cap pin. The zero-survival branch is not
treated. The collar is a source-matched reduction and the two-cut calculation
is a no-go for that immediate repair, not a consumer of the paid port.
