# Finite-clock paid ports generate a fixed-scale response curl

Identity: `CODEX_DESCENDANT`

Date: 2026-08-31

Status: **ordinary mathematics proved below after review; not a terminal
consumer.**  In the maintained Fin4 no-uniform-payoff hard residual, a
finite-clock off-minimum paid port can be kept source-attached and converted
to a literal four-profile response rectangle with a uniform positive curl.
Common-prefix minimization then yields either the reset-rigid global-minimum
chamber or a strict unique-all-Continue descendant carrying a closed
four-point semantic/law curl passport.  The finite quartet is executable; its
compact limit need not be.  This connects the finite-clock deadline descent
to the existing strict-inert waist; it does not consume either output.

## 1. Question

Assume the maintained four-player no-uniform-payoff hard residual, including
its terminal exploitability witness and all-player punishment normality.  Its
global terminal-semantic minimum is positive:

\[
 D_*:=\min_\sigma D(\sigma)>0.
\]

The finite-clock deadline theorem starts from an actual finite-clock global
minimum and produces an actual finite-clock off-minimum profile, a complete
pure-time best response of gain greater than \(D_*/4\), and literal finite
ancestry from the minimum.  Can one consume that paid port without replacing
it by an unrelated minimum or losing its actual source?

Start from the actual finite-clock minimum source and its source-attached
off-minimum paid port supplied by the finite-clock deadline descent.  The
result below does not give a terminal consumer.  It gives a stronger
source-faithful reduction than the generic paid-cap trichotomy: the port
enters a fixed-scale common-response rectangle, and hence a normalized
closed-descendant minimizer with unique all-Continue cap root.

## 2. A bounded-calendar response cycle from every finite-clock source

Let \(\sigma^0\) be any actual finite-clock profile.  Fix \(H_0\) such that
every finite stopping time in its four prescribed stopping laws is at most
\(H_0\).

Against finite-clock opponents, every behavioral payoff is an average of
pure-time and Never payoffs.  If the opponents have no finite stopping mass
after \(H\), a pure-time best response can be chosen from

\[
 \{0,1,\ldots,H+1\}\cup\{\infty\}.
\tag{2.1}
\]

Indeed, all finite times strictly after \(H\) have the same payoff: either an
opponent has already stopped, or the deviator eventually stops alone.  Use
the deterministic tie convention: choose Never whenever it ties a finite
maximizer, and otherwise choose the least finite maximizer.

Fix an ordering of the four players and use its least maximum-debt player at
every tie.  Starting at \(\sigma^0\), repeatedly choose that player and
replace only it by the selected pure-time exact best response.  Every current
profile is an actual carrier point, so its total debt is at least \(D_*\).
Consequently every selected mover gain is at least

\[
 \delta:=D_*/4.
\tag{2.2}
\]

The calendar never grows past \(H_0+1\).  To see this, an action at
\(H_0+1\) can only have been installed as a pure response.  If the current
mover is not its owner, that sure opponent makes every later finite time have
the same law as Never, so the tie convention chooses Never.  If the mover is
its owner and no other player uses \(H_0+1\), deleting the mover's own
strategy leaves opponent horizon at most \(H_0\), so (2.1) again gives a
response no later than \(H_0+1\).  The same argument covers several owners at
that date.

Every coordinate is therefore either its one original finite-clock strategy,
one of the finitely many pure times \(0,\ldots,H_0+1\), or Never.  The
deterministic recursion visits a finite state space.  Every edge has strictly
positive gain, so a repeated state yields a nontrivial literal cycle

\[
 \sigma^0_{\rm cyc},\sigma^1_{\rm cyc},\ldots,
 \sigma^{m}_{\rm cyc}=\sigma^0_{\rm cyc}.
\tag{2.3}
\]

If player \(i_k\) moves on edge \(k\), write

\[
 g_k=U_{i_k}(\sigma^{k+1}_{\rm cyc})
       -U_{i_k}(\sigma^k_{\rm cyc})\ge\delta.
\tag{2.4}
\]

Because the mover's opponents are unchanged, its cap is unchanged and its
target debt is zero.

This cycle is horizontal.  No vertex or edge is being called a temporal
Nash--Bellman root.

The finite-cycle construction itself needs only a finite-clock starting
profile and the positive global debt floor.  It does not use the earlier paid
port.  Starting at the deadline port is nevertheless important for the final
statement: it retains the particular minimum-source ancestry rather than
producing an unrelated horizontal cycle elsewhere in the table.

## 3. A fixed recipient-debt rise

For a nonmover \(h\ne i_k\), put

\[
 \Delta_{k,h}=d_h(\sigma^{k+1}_{\rm cyc})
                -d_h(\sigma^k_{\rm cyc}).
\]

The exact one-player leakage identity is

\[
 D(\sigma^{k+1}_{\rm cyc})-D(\sigma^k_{\rm cyc})
 =-g_k+\sum_{h\ne i_k}\Delta_{k,h}.
\tag{3.1}
\]

Summing around the literal cycle gives

\[
 \sum_{k<m}\sum_{h\ne i_k}\Delta_{k,h}
 =\sum_{k<m}g_k\ge m\delta.
\tag{3.2}
\]

There are exactly \(3m\) ordered edge--recipient pairs.  Hence some fixed
edge and nonmover satisfy

\[
 d_j(E)-d_j(S)\ge\delta/3=D_*/12,
\tag{3.3}
\]

where \(S\) is the source and \(E\) the target of that edge.  Let \(p\) be
the edge mover.  Then

\[
 U_p(E)-U_p(S)=g\ge D_*/4.
\tag{3.4}
\]

This is stronger than merely selecting a debtor at an arbitrary off-minimum
profile: the debtor rise and the paid mover edge occur on the same literal
source transition.

## 4. The exact four-profile curl

Choose a pure-time or Never exact best response \(a_j\) of player \(j\)
against \(E_{-j}\).  Such a response exists by (2.1).  Define

\[
 R=(a_j,E_{-j}),
 \qquad
 Q=(a_j,S_{-j}).
\tag{4.1}
\]

The four profiles \((R,Q,E,S)\) are literal finite-clock profiles.  Since
\(p\ne j\), the two unilateral replacements commute: \(R\) is obtained from
\(Q\) by applying the same \(p\)-strategy replacement which sends \(S\) to
\(E\).  Moreover

\[
 d_j(R)=0.
\tag{4.2}
\]

Define the common-response payoff curl

\[
 \mathcal C=
 [U_j(R)-U_j(E)]-[U_j(Q)-U_j(S)].
\tag{4.3}
\]

The first bracket equals \(d_j(E)\).  The response \(a_j\) at \(Q\) need
not be optimal against \(S_{-j}\), but

\[
 U_j(Q)-U_j(S)\le d_j(S).
\]

Thus (3.3) gives the exact fixed floor

\[
 \boxed{\mathcal C\ge D_*/12.}
\tag{4.4}
\]

Together, (3.4), (4.2), and (4.4) are a literal source-attached rectangle:

\[
 d_j(R)=0,
 \qquad
 \mathcal C\ge D_*/12,
 \qquad
 U_p(E)-U_p(S)\ge D_*/4.
\tag{4.5}
\]

The original finite-clock paid port and the original global-minimum profile
remain recoverable by the finite response ancestry leading to the cycle.

There is also a finite terminal-coordinate decoder.  Writing the payoff curl
as the reward moment of

\[
 \mu_R-\mu_E-\mu_Q+\mu_S,
\]

one of the fifteen nonempty terminal coalitions \(T\) has

\[
 [\mu_R(T)-\mu_E(T)-\mu_Q(T)+\mu_S(T)]r_j(T)
 \ge D_*/192.
\tag{4.6}
\]

The Never coordinate contributes zero under the normalized terminal payoff.
Equation (4.6) is a four-law curl coordinate.  It must not be weakened to a
two-law difference such as \((\mu_R-\mu_Q)r_j(T)\) without an additional
argument.

## 5. Common-prefix descendant minimization

Prefix one arbitrary finite product-root word \(W\) to all four profiles.
Both positive coordinates scale by the same joint survival \(c(W)\):

\[
 \mathcal C(W\star R,W\star Q,W\star E,W\star S)
 =c(W)\mathcal C(R,Q,E,S),
\tag{5.1}
\]

\[
 U_p(W\star E)-U_p(W\star S)
 =c(W)[U_p(E)-U_p(S)].
\tag{5.2}
\]

The fresh-root payoff terms cancel in each alternating difference.  Take the
closure of this four-profile common-prefix orbit in the fourfold joint
semantic/law carrier.  Choose small positive \(\theta,\psi\) and minimize
the first-coordinate debt on the compact slice

\[
 d_j(R)=0,
 \qquad
 \mathcal C\ge\theta D(R),
 \qquad
 U_p(E)-U_p(S)\ge\psi D(R).
\tag{5.3}
\]

The slice is nonempty by (4.5).  Choose one common subsequence on which all
four semantic pairs and terminal laws converge, and let
\((r,q,e,s)\) denote the resulting four-point minimizer.  These are four
joint semantic/law points with closed common-prefix provenance.  They need
not be represented by four behavioral profiles retaining the original
commuting replacements.

If \(x\) is exact cap--Nash against the cap of the first point \(r\), common
prefixing by \(x\) preserves the closed slice: the first-coordinate debt,
its zero \(j\)-coordinate, and both scalar passports scale by the joint
survival.  Minimality and positive debt therefore force that survival to
equal one.
Hence

\[
 \boxed{x\text{ exact at }B(r)
        \iff x=\mathbf C.}
\tag{5.4}
\]

Finite root-game Nash existence supplies the reverse implication.

There are now two exact numerical landings.

1. If \(D(r)=D_*\), hard-residual finite-atom existence and the global
   singleton margin imply positive total opponent incidence for the zero-debt
   observer \(j\).  Indeed zero incidence would force every positive finite
   atom to be \(\{j\}\), and singleton/Never cap tightness would contradict
   the margin.  The retained hard residual and terminal exploitability
   witness then place this point in the law-tight reset-rigid chamber.
2. If \(D(r)>D_*\), one obtains a strict off-minimum descendant with zero
   \(j\)-debt, unique all-Continue cap root, and both fixed positive
   debt-relative **closed four-point passports** from (5.3).

This is the same compact minimization mechanism as the reviewed four-profile
descendant-slice theorem, with the aggregate response curl retained as the
first passport rather than an unjustified two-law atom difference.  At the
limit, the passport is the alternating payoff/law identity along the one
common subsequence; it is not a literal executable response rectangle.

## 6. Consequence and precise blocker

Combining the finite-clock deadline descent with Sections 2--5 gives

\[
\boxed{
\begin{array}{c}
\text{actual finite-clock positive global minimum}
\\ \Downarrow \\
\text{literal off-minimum paid port}
\\ \Downarrow \\
\text{reset-rigid global-minimum chamber}
\quad\text{or}\quad
\text{strict unique-all-Continue closed curl passport}.
\end{array}}
\tag{6.1}
\]

All arrows before taking the final common-prefix closure retain finite actual
ancestry.  The last quartet has one common-subsequence, closed-descendant
provenance, not four literal strategies or one recovered finite prefix code.

This does **not** prove a charged return, a renewable finite rank, or a
uniform-equilibrium payoff.  A positive static response curl is not an exact
Nash--Bellman chronology.  The exact regression in
`CODEX_DESCENDANT__ASYMPTOTIC_PROJECTIVE_PASSPORT_AND_ROOT_BARRIER.md`
already realizes a positive curl together with a unique all-Continue root and
fixed-cap barrier when the global minimum is zero.  Hence any consumer must
use the retained positive-minimum ancestry, not only the local rectangle.

The remaining direct question is now sharp: consume either the reset-rigid
landing or the strict unique-all-Continue closed curl passport while
preserving the incoming finite ancestry, or show that one of them carries a
renewable law/chronology rank.

## 7. Sources inspected and Lean boundary

The ordinary proof uses the checked pure-time extremality and actual-profile
cap interfaces behind:

* `sSup_range_quittingTerminalPayoff_update_eq_pureTime`;
* self-update invariance of `quittingContinuationBestResponseValue`;
* the exact one-player debt-leakage identity;
* common-prefix payoff and law scaling; and
* exact cap--Nash debt scaling.

The bounded-calendar selection is the same finite support argument used in
the reviewed canonical finite-clock response chain.  The new mathematics is
the cycle sum (3.2), the fixed recipient rise (3.3), the exact curl estimate
(4.4), and its composition with the common-prefix minimizer.

Lean-sized declarations would be:

```text
finiteClock_exists_boundedCalendar_exactResponseCycle
finiteClockResponseCycle_exists_recipientDebtRise
recipientDebtRise_exists_positiveCommonResponseCurl
positiveCurlQuartet_exists_resetRigid_or_strictUniqueAllContinueClosedPassport
```

No declaration implementing these compositions is claimed to exist.
