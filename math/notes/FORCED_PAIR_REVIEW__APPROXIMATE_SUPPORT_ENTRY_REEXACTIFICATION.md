# Re-exactifying a support-entry restart without lifting its root

Author: FORCED_PAIR_REVIEW

## Status

A support-entry root at an off-minimum carrier limit cannot be approximated by
fixed-charge exact roots at the original actual caps. Nevertheless, the
source can be re-exactified after the state change:

1. prefix the fixed limit root literally to the actual prelimit profiles;
   it is only asymptotically cap--Nash, but its exact cap-defect error tends
   to zero and it makes the desired strict debt drop in the limit;
2. against each resulting changed actual profile, choose a fresh exact
   cap--Nash root and prefix it once.

Positive global minimum debt forces every fresh exact root to have a
uniformly positive all-Continue probability. Therefore this second prefix
cannot erase the retained pair mass, minimum tail, or paid row. It also
cannot undo the first prefix's strict debt drop.

The result is a source-attached exact restart. If its limiting whole debt is
\(D_*\), it feeds the existing three-role compiler. Otherwise it is a new
off-minimum source at a strictly smaller debt level, to which the maximal-ray
construction can be applied again.

The normalized pair-mass/debt and paid-gain/debt passports survive exactly in
the limit. Repeated support-entry restarts therefore do not lose the causal
scale, although strictly decreasing real debt is still not a well-founded
rank.

This is ordinary mathematics. Its identities compose checked declarations,
but the dependent forced-pair restart is not yet one Lean theorem.

## 1. Input

Let \(z_*\) be a global terminal-semantic minimum with

\[
D_*:=D(z_*)>0.
\]

Let \(X_n\) be actual behavioral profiles such that

\[
\operatorname{Sem}(X_n)\longrightarrow z,
\qquad
D(X_n)\longrightarrow L:=D(z)>D_*.
\tag{1}
\]

Assume a fixed product root \(q\) is exact cap--Nash at the limiting cap:

\[
q\in\operatorname{Nash}(z^B),
\qquad
a:=\operatorname{Abs}(q)>0.
\tag{2}
\]

Write \(c:=\operatorname{Cont}(q)=1-a\). The carrier-prefix argument gives

\[
0<c<1,
\qquad
D':=cL\ge D_*.
\tag{3}
\]

For the forced-pair application, additionally suppose \(X_n\) carries:

* a fixed pure pair \(C=\{j,o\}\) at a marked date \(t_n\);
* unconditional pair mass \(M_n\ge M_0>0\);
* a literal minimum-return post-pair tail \(\sigma_n\);
* zero marked root defect for the selected owner \(o\); and
* a fixed mover \(p\) with a literal one-date gain \(g_n\ge g_0>0\).

## 2. The fixed support-entry root is quantitatively approximate

Let \(b_n=(\operatorname{Sem}X_n)^B\). For each player define

\[
e_{n,i}:=\delta_i(b_n,q),
\qquad
\eta_n:=\max_i e_{n,i},
\qquad
E_n:=\sum_i e_{n,i}.
\tag{4}
\]

Root-coordinate Nash defect is continuous in the cap and root. Since
\(b_n\to z^B\) and \(q\) is exact at \(z^B\),

\[
e_{n,i}\to0,
\qquad
\eta_n\to0,
\qquad
0\le E_n\le |I|\eta_n\to0.
\tag{5}
\]

Thus \(q\) is an \(\eta_n\)-Nash root at the actual cap, in the exact
coordinate-defect sense. No nearby exact-root selection is asserted.

Define literal changed profiles

\[
Y_n:=q\triangleright X_n.
\tag{6}
\]

The checked arbitrary-root decomposition
quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul gives

\[
d_i(Y_n)=e_{n,i}+c\,d_i(X_n).
\tag{7}
\]

Summing,

\[
\boxed{D(Y_n)=E_n+cD(X_n).}
\tag{8}
\]

By (1) and (5),

\[
D(Y_n)\longrightarrow cL=D'<L.
\tag{9}
\]

The strict limiting drop is \(L-D'=aL>0\). The approximate Nash error has
therefore been accounted for exactly as the additive nonnegative term
\(E_n=o(1)\).

## 3. The approximate prefix retains the causal passport

The pure pair moves from date \(t_n\) to date \(t_n+1\). Its exact mass is

\[
M_n^Y=cM_n\ge cM_0>0.
\tag{10}
\]

The complete live-root spine after the pair remains \(\sigma_n\). The pair,
labels, local root defects, and endpoint orientation are unchanged.

Both the source and its mover update share outer root \(q\), so their payoff
difference scales by joint Continue:

\[
g_n^Y=cg_n\ge cg_0>0.
\tag{11}
\]

The update still changes only player \(p\)'s complete behavioral strategy.
Its unrestricted cap against the fixed opponents is unchanged, and exact
own-debt subtraction remains valid.

Thus \(Y_n\) is already a lower-debt actual source. Its only defect as an
exact chronological restart is that \(q\) is not exact at \(b_n\).

## 4. Fresh exactification at the changed continuation

For every \(n\), choose an exact cap--Nash root \(r_n\) against the complete
behavioral cap of \(Y_n\). One may take the canonical maximal-absorption
selector. Define

\[
s_n:=\operatorname{Cont}(r_n),
\qquad
Z_n:=r_n\triangleright Y_n.
\tag{12}
\]

Now \(r_n\) is an exact root against its actual continuation cap. Exact
cap--Nash scaling gives

\[
\boxed{D(Z_n)=s_nD(Y_n).}
\tag{13}
\]

Since \(Z_n\) is actual, global minimality gives

\[
D_*\le s_nD(Y_n).
\tag{14}
\]

Because \(D(Y_n)\to D'>0\), eventually \(D(Y_n)\le2D'\). Therefore

\[
\boxed{s_n\ge {D_*\over D(Y_n)}
\ge {D_*\over2D'}=:s_0>0.}
\tag{15}
\]

The fresh exact root may be far from \(q\), but its survival cannot vanish.
Thus it cannot destroy the causal packet.

Also \(D(Z_n)\le D(Y_n)\). Combining this with (9), eventually

\[
D(Z_n)\le {L+D'\over2}<L.
\tag{16}
\]

Exactification cannot undo the strict state change.

## 5. Exact source fields after re-exactification

The pair is now at date \(t_n+2\), with exact mass

\[
M_n^Z=s_ncM_n\ge s_0cM_0>0.
\tag{17}
\]

Its post-pair tail remains literally \(\sigma_n\). The owner root defect is
still zero, and the mover gain is

\[
g_n^Z=s_ncg_n\ge s_0cg_0>0.
\tag{18}
\]

Exact own-debt subtraction survives. Thus \(Z_n\) retains:

* the old minimum point and minimum-return tail;
* the fixed pair, owner, mover, and orientation;
* fixed positive pair-mass and paid-gain floors;
* a literal fresh exact cap--Nash outer root; and
* whole-source debt uniformly below the old limit \(L\).

No exact root near \(q\) was selected. This is why old-cap
non-lower-hemicontinuity does not obstruct the construction.

## 6. Limit and normalized passports

Pass to a subsequence with \(s_n\to s\). Equation (15) gives \(s\ge s_0>0\).
Equations (9) and (13) give

\[
D(Z_n)\longrightarrow L_1:=sD',
\qquad
D_*\le L_1\le D'<L.
\tag{19}
\]

After further subselection, write \(M_n\to M>0\) and \(g_n\to g>0\). Then

\[
M_n^Z\to scM,
\qquad
g_n^Z\to scg.
\tag{20}
\]

Since \(D'=cL\),

\[
\boxed{
{scM\over sD'}={M\over L},
\qquad
{scg\over sD'}={g\over L}.
}
\tag{21}
\]

Thus pair-mass/debt and paid-gain/debt densities are exactly invariant through
both the approximate support-entry prefix and fresh exactification. In
particular

\[
scM={M\over L}L_1\ge {M\over L}D_*>0,
\tag{22}
\]

and similarly for the gain. The causal passport cannot evaporate under
repeated support-entry restarts.

## 7. Consumer split

If \(L_1=D_*\), the actual profiles \(Z_n\) have whole debt tending to
\(D_*\), a fixed pair of positive mass, the minimum-return tail, zero marked
owner defect, and a fixed paid mover gain. These are the fields required by
the maintained concentrated-collision/three-role compiler.

If \(L_1>D_*\), the family \(Z_n\) is an actual off-minimum source at a
strictly smaller level \(L_1<L\), with all causal fields and a fresh exact
outer root. The generic changed-state maximal-prefix construction can be run
again from this source and retains its pair atom by the checked debt-ratio
bound.

This is a genuine iterative restart, not merely an abstract carrier point.
It does not finish the conjecture because strictly decreasing real debt is
not well founded. For infinitely many restarts one still needs convergence
to \(D_*\), charged recurrence, or a finite-rank event. Equation (21) shows
that loss of the pair passport is no longer an obstruction.

## 8. Why small nearby corrections are unnecessary

At the old caps, maximality proves every exact root has absorption tending to
zero, so no root correction tending to \(q\) can make it a fixed-charge exact
root there.

The construction changes the continuation first and invokes exact Nash
existence at \((\operatorname{Sem}Y_n)^B\). The fresh root \(r_n\) need not be
close to \(q\). If the demand is that the corrected root itself be
\(o(1)\)-close to \(q\), that is impossible. If the demand is an exact
source-attached restart preserving progress and causal data, one fresh outer
exact root is sufficient and always exists.

## 9. Lean-facing target

A dependent structure QuittingSupportEntryReexactifiedRestart should retain
\(X_n,Y_n,Z_n\), roots \(q,r_n\), errors \(e_{n,i}\), debt equations
(8), (13), marked dates, pair masses, post-pair tail equality, paid gains,
and survival lower bound (15).

The source-facing theorem
exists_supportEntry_reexactified_minimumReturn_or_lowerSource should return
either the existing minimum-return packet or a new off-minimum source with
limiting debt \(L_1<L\) and the same normalized passports.

Checked ingredients:

* quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul;
* continuity of quittingRootCoordinateNashDefect;
* exists_isZeroQuittingRootNash or the maximal-root selector;
* quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_of_capNash;
* the global minimum lower bound for actual profiles;
* exact mass and payoff-difference scaling under common prefixes; and
* quittingTerminalSemanticDebt_stageBestEndpoint_eq_sub_gain.

## 10. Verdict

The support-entry seam can be re-exactified source-faithfully:

\[
\boxed{
\begin{array}{c}
\text{positive support-entry root, asymptotically exact at }X_n\\
\Downarrow\\
\text{literal lower-debt sources }Y_n\\
\Downarrow\ \text{one fresh exact root at each changed cap}\\
\text{exact-root sources }Z_n.
\end{array}}
\]

The remaining issue is no longer exactification. It is termination of
repeated strict off-minimum restarts:

\[
\boxed{
\text{infinitely many lower source levels}
\Longrightarrow
\text{minimum return, charged recurrence, or finite-rank event}.
}
\]

## Sources inspected

* Research/Quitting/CausalTailEscapeMaxAbsorptionCore.lean.
* UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticOwnStrategyTransport.lean.
* UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean.
* UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiveWeightedCollisionTransfer.lean.
* exports/FIN4_FORCED_PAIR_MAXIMAL_PREFIX_RAY_DICHOTOMY.md.

