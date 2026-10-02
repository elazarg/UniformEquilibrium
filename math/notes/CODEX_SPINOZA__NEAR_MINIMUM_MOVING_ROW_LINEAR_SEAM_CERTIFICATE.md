# Near-minimum moving rows pay a linear source seam or support error

Identity: `CODEX_SPINOZA`

## Current status

**Ordinary mathematics; direct quantitative consequence of checked
declarations, plus an exact response-curl localization; no complete Fin4
consumer.**  This note answers the one-row approximate producer requested
after exact source reprojection was excluded.  Near the positive minimum
fibre, no positive-absorption moving row can have both support-Nash error and
source/passport seam little-oh of its absorption.

The conclusion is uniform over all actual carrier sources in a fixed debt
collar.  It does not assume that the row is exact, and adding an exact Bellman
successor does not weaken the obstruction.

Sections 9--11 audit the new two-coordinate response-curl fork.  Its premark
total-variation arm is **not** by itself the payoff collar in Theorem 2.1.
The curl does, however, localize it to either a paid one-player update no
later than the old mark or a near-neutral premark externality edge.  The paid
arm strictly lowers the clock unless its first disagreement is the marked row
itself.  That same-row case and the externality arm are the remaining
source-attached adapters; positive minimum alone has not yet paid them.

Sections 13--16 then test a global topological repair.  A compact
payoff/root relation alone is too weak: the outer cap carries a canonical
zero-charge all-Continue recurrent point, while the operation returning from
that payoff annotation to the actual source is not a Bellman edge.  An exact
charged-return theorem is proved for one **actual composable orbit**; this
pinpoints the extra restart hypothesis which ordinary chain recurrence does
not supply.

## 1. Exact question

Assume a four-player quitting reward table has no uniform-equilibrium payoff.
Let \(D_*>0\) be its minimum total terminal-semantic debt.  An actual source
is a carrier pair

\[
 s=(u,b),
\]

where \(u\) is the prescribed payoff and \(b\) its unrestricted cap vector.

Consider a proposed moving forward row consisting of:

* an evaluation tail \(v\in\mathbb R^4\);
* a product root \(q\);
* absorption \(h=a(q)>0\);
* support-local Nash tolerance \(\delta\ge0\); and
* source/passport seam \(e=\operatorname{dist}(v,u)\).

The row may additionally carry the exact Bellman successor

\[
 v^+=F(q,v).
\]

Can a source sequence with \(D(s_n)\to D_*\) admit rows for which

\[
 \frac{\delta_n}{h_n}\to0,
 \qquad
 \frac{e_n}{h_n}\to0?
 \tag{1.1}
\]

The answer is no.

## 2. Uniform seam-or-error certificate

### Theorem 2.1

There are constants \(\eta>0\) and \(\lambda>0\), depending only on the
reward table, such that for every actual carrier source \(s=(u,b)\) with

\[
 D(s)<D_*+\eta,
 \tag{2.1}
\]

and every product root \(q\) satisfying

\[
 \operatorname{IsSupportApproxNash}(r,v,\delta,q),
 \qquad \delta\ge0,
\]

one has

\[
 \boxed{
 \lambda\,a(q)
 \le \operatorname{dist}(v,u)+\delta .}
 \tag{2.2}
\]

One may choose constants \(c,\rho>0\) from the checked minimum-fibre linear
absorption-defect tube and take

\[
 \lambda=\min\{\rho/2,c/4\}.
 \tag{2.3}
\]

The statement is independent of the value chosen for the exact Bellman
successor \(F(q,v)\).

### Proof

The declaration
`exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff`
supplies:

* the compact minimum-fibre payoff projection \(K\);
* an open neighborhood \(N\);
* constants \(c,\rho>0\);
* \(\operatorname{thickening}_\rho(K)\subseteq N\); and
* for every \(v\in N\) and product root \(q\),

  \[
  c\,a(q)\le \operatorname{Def}(v,q),
  \tag{2.4}
  \]

  where \(\operatorname{Def}\) is the total one-stage Nash defect.

Apply
`exists_pos_carrierDebtMoat_of_infDist_minimumFiber` with this \(\rho\).
After shrinking to one \(\eta>0\), (2.1) implies

\[
 \operatorname{infDist}(u,K)<\rho/2.
 \tag{2.5}
\]

Put \(e=\operatorname{dist}(v,u)\) and \(h=a(q)\).  There are two cases.

If \(e\ge\rho/2\), then \(0\le h\le1\), so

\[
 \min\{\rho/2,c/4\}\,h\le (\rho/2)h\le e\le e+\delta.
\]

If \(e<\rho/2\), the one-Lipschitz estimate for distance to \(K\), together
with (2.5), gives

\[
 \operatorname{infDist}(v,K)<\rho,
\]

and hence \(v\in N\).  Support-local \(\delta\)-Nash implies ordinary
endpoint \(\delta\)-Nash by
`isQuittingRootEndpointNash_of_supportApproxNash`; the endpoint/root
equivalence then gives `IsεQuittingRootNash reward v δ q`.  Therefore
`quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash` yields, for
four players,

\[
 \operatorname{Def}(v,q)\le4\delta.
 \tag{2.6}
\]

Combining (2.4) and (2.6),

\[
 \frac c4 h\le\delta\le e+\delta.
\]

Both cases prove (2.2).  \(\square\)

## 3. Sequential exclusion

### Corollary 3.1

Let \(s_n=(u_n,b_n)\) be actual carrier sources with

\[
 D(s_n)\longrightarrow D_*.
\]

Let \((v_n,q_n,\delta_n)\) be moving rows with \(h_n=a(q_n)>0\),
\(\delta_n\ge0\), and support-local \(\delta_n\)-Nash at \(v_n\).  Then it is
impossible that

\[
 \frac{\operatorname{dist}(v_n,u_n)}{h_n}\longrightarrow0
 \quad\hbox{and}\quad
 \frac{\delta_n}{h_n}\longrightarrow0.
 \tag{3.1}
\]

Indeed Theorem 2.1 applies eventually and division of (2.2) by \(h_n>0\)
gives

\[
 \lambda\le
 \frac{\operatorname{dist}(v_n,u_n)}{h_n}+
 \frac{\delta_n}{h_n},
\]

contradicting (3.1).

This remains true if every row has exact Bellman matching
\(v_n^+=F(q_n,v_n)\), because the obstruction is already present before the
successor is formed.

## 4. A finite deviation certificate

The scalar inequality has a playerwise witness.  In the near-source case
\(e<\rho/2\), (2.4) says

\[
 c h\le\sum_{i\in\operatorname{Fin}4}
   \operatorname{Def}_i(v,q).
\]

Thus some player \(i\) satisfies

\[
 \operatorname{Def}_i(v,q)\ge(c/4)h.
 \tag{4.1}
\]

The coordinate defect is exactly that player's best pure root action value
minus its prescribed mixed value.  Hence (4.1) is a literal one-stage pure
deviation certificate.  Along any infinite candidate family, a subsequence
fixes the same player, and then one of the two pure actions may also be fixed.

This is the requested separating certificate: a candidate row must either
cross the fixed geometric collar \(\rho/2\), or expose a pure one-stage
deviation of size at least \((c/4)h\).  It is not an annotation-only label.

## 5. Consequence for the tangent paid port

At a tangent full-replacement endpoint with minimum limiting debt, the
literal paid-row sources converge into the debt collar (2.1).  The paid row
still carries its fixed observer, fixed gain, source-support witness, and
quantitative reach bounds.  Nevertheless any attempt to attach a
positive-absorption approximate Nash--Bellman row with both a sublinear
source rebase and sublinear support error violates (2.2).

Therefore the paid first-disagreement row cannot be converted locally into
the desired approximate forward row.  A successful forward packet must begin
with a **macroscopic exit** from the minimum tube and charge that exit in an
accepted global ledger, or exploit an off-minimum source already outside the
tube.  Renewal solely by ever smaller local rows at the minimum is excluded.

## 6. Scope and nonclaims

* The theorem excludes the little-oh-in-absorption producer, not the fixed
  tolerance packet requested in the main question.  For a prescribed
  \(\delta>0\), rows with \(h\ll\delta\) are compatible with (2.2).
* No claim is made once the evaluation tail crosses the fixed source collar;
  this is exactly the macroscopic-seam branch.
* Exact Bellman matching is allowed but not used.  The theorem supplies no
  renewal rule at the literal successor.
* The player/action witness may depend on the row; only a subsequence makes
  it persistent.
* No uniform-equilibrium payoff or negative counterexample is produced.

## 7. Files and declarations inspected

* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberLinearAbsorptionDefect.lean`:
  `exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff`.
* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourCarrierSourceChargeDebtErrorGate.lean`:
  `exists_pos_carrierDebtMoat_of_infDist_minimumFiber`.
* `UniformEquilibrium/Quitting/Boundary/Repair/SupportEnlargementAlternative.lean`:
  `IsQuittingRootSupportApproxNash`.
* `UniformEquilibrium/Quitting/Paths/SupportWitnessClockCollapse.lean`:
  `isQuittingRootEndpointNash_of_supportApproxNash`.
* `UniformEquilibrium/Quitting/Root/NashDefect.lean`:
  `quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash`.
* `questions/FIN4_APPROXIMATE_FORWARD_PACKET_OR_CAPACITY_BARRIER.md`.

## 8. Next exact question

Can the fixed macroscopic collar crossing \(e\ge\rho/2\) be paid from the
source's terminal exploitability or retained atom in a way that lands at the
literal Bellman successor and is renewable?  Theorem 2.1 proves that no
local \(o(h)\) interpolation can replace that crossing.

## 9. Premark curl localization is stronger than a TV seam

This section uses the notation of Section 7.18.10 of
`CODEX_SNELL__AGGREGATE_PAID_ORIENTATION_FINITE_ATOM_AND_NORMALIZED_PASSPORT.md`.
Fix two strategies \(s,r\) of player \(j\), two strategies \(a,b\) of a
different player \(k\), and the other two players.  Write

\[
 F(x,y)=U_j(x,y),
 \qquad
 \chi=F(r,b)-F(r,a)-F(s,b)+F(s,a).
 \tag{9.1}
\]

For a cut \(m\), let

\[
 r_m=\operatorname{Sp}_m(s,r),
 \qquad b_m=\operatorname{Sp}_m(a,b),
\]

and let

\[
 \chi_m=F(r_m,b_m)-F(r_m,a)-F(s,b_m)+F(s,a).
 \tag{9.2}
\]

The splice agrees with the source law at every date below \(m\) and uses the
alternative's conditional continuation at and after the cut.

### Theorem 9.1 (postmark block, premark payment, or premark externality)

Suppose \(|\chi|\ge C>0\).  At least one of the following holds.

1. \(|\chi_m|\ge C/2\).  This is the common-prefix postmark arm already
   converted in Snell's Section 7.18.10 into a reached two-cut block and then
   into an off-minimum exit or paid splice.
2. There are two actual profiles differing in one complete strategy whose
   first behavioral disagreement is strictly before \(m\), and one
   orientation of that update pays its mover at least \(C/16\).
3. There are two actual profiles differing only in player \(k\)'s complete
   strategy, again with first disagreement strictly before \(m\), such that,
   in one orientation,

   \[
    U_j(H[k\leftarrow\rho])-U_j(H)\ge C/8,
    \qquad
    \left|U_k(H[k\leftarrow\rho])-U_k(H)\right|<C/16.
    \tag{9.3}
   \]

Thus the unconsumed output is not merely a metric TV label.  It is a literal
premark, near-neutral-mover externality edge with a fixed observer gain.

### Proof

If the first arm fails, then

\[
 |\chi-\chi_m|\ge C/2.
 \tag{9.4}
\]

There is an exact four-edge expansion

\[
\begin{aligned}
 \chi-\chi_m={}&[F(r,b)-F(r_m,b)]
                 +[F(r_m,b)-F(r_m,b_m)]\\
               &+[F(r_m,a)-F(r,a)]
                 +[F(s,b_m)-F(s,b)].
\end{aligned}
\tag{9.5}
\]

Hence one bracket has absolute value at least \(C/8\).  The first and third
brackets are player \(j\)'s own payoff along a one-player update, so either
orientation gives arm 2 (in fact with gain at least \(C/8\)).  The second and
fourth brackets are player \(j\)'s payoff along a one-player \(k\)-update.
Orient the selected edge so that \(j\)'s gain is at least \(C/8\).  If the
absolute change in \(k\)'s own payoff is at least \(C/16\), orienting that edge
by \(k\)'s sign gives arm 2.  Otherwise (9.3) holds.

For every edge in (9.5), the changed pair is either \(r,r_m\) or \(b,b_m\).
If its payoff difference is nonzero, the two laws are distinct.  Since the
splice uses the alternative conditional law after \(m\), distinctness forces
a first discrepancy in the finite atoms below \(m\).  The reconstructed
behavioral strategies therefore first disagree strictly before the old cut.
\(\square\)

The proof does not use the weaker estimate

\[
 |\chi-\chi_m|\le4M(\delta_j+\delta_k).
\]

That estimate detects failure of common-prefix replacement, whereas (9.5)
detects the actual payoff edge responsible for the failure.

## 10. Why premark TV is not the collar in Theorem 2.1

There are two independent exact obstructions to identifying Snell's first
arm directly with the payoff seam
\(\operatorname{dist}(v,u)\) in (2.2).

### 10.1 Exact survival/reshuffling decomposition

For two one-player laws \(\mu_0,\mu_1\), write

\[
 d_t=\mu_1(t)-\mu_0(t)\quad(t<m),
 \qquad
 d_*=\mu_1([m,\infty])-\mu_0([m,\infty]).
\]

Put

\[
 P=\sum_{t<m}(d_t)^+,
 \qquad N=\sum_{t<m}(d_t)^-.
\]

Mass conservation gives \(d_*=N-P\), and direct calculation gives

\[
 \boxed{
 \delta_m(\mu_0,\mu_1)
 =\max\{P,N\}
 =|d_*|+\min\{P,N\}.}
 \tag{10.1}
\]

The first term is the change in survival to the cut.  The second is balanced
transport among premark dates.  When the two laws have the same conditional
continuation after \(m\), as an alternative and its canonical splice do,
every event wholly in that common suffix sees only \(d_*\): with the other
strategies fixed, if its conditional probability given this player's
survival is \(\beta\), its probability changes by exactly \(\beta d_*\).
The balanced term can therefore be arbitrarily large while being completely
invisible to every postcut retained event.

An atom ending at the marked row is one additional affine functional of the
prefix law, not a norm.  It likewise supplies no lower bound on (10.1): a
prefix simplex of dimension at least two has nonzero directions in the
kernel of one such functional.

### 10.2 Unit TV can have zero terminal-law and payoff seam

There is a table-independent finite-dimensional statement.  Fix one player's
opponents and choose seventeen pure stopping dates below \(m\).  Send a pure
date to the induced terminal outcome law on the fifteen nonempty coalitions
plus Never.  These laws lie in an affine space of dimension at most fifteen.
Radon's theorem gives two disjoint collections of the seventeen dates and
convex weights on them with the same induced terminal law.  Let the resulting
two stopping laws be \(\mu_0,\mu_1\).  Their supports are disjoint, so

\[
 \operatorname{TV}(\mu_0,\mu_1)=1,
 \tag{10.2}
\]

while the complete terminal outcome law is identical.  Consequently every
prescribed payoff coordinate, and every retained terminal atom coordinate,
is identical as well.

This construction does **not** preserve all unrestricted cap coordinates:
an opponent's cap tests all of that opponent's counterfactual responses.
It therefore is not a positive-\(D_*\) game regression.  It proves the exact
interface fact needed here: no inequality of the form

\[
 \operatorname{dist}(U(\mu_0),U(\mu_1))
 \ge \kappa\operatorname{TV}(\mu_0,\mu_1)
 \tag{10.3}
\]

can follow from terminal-law or retained-atom data, for any \(\kappa>0\).
Only the reverse Lipschitz inequality is automatic.  Thus the TV threshold in
Snell's premark arm cannot be substituted for the collar
\(\operatorname{dist}(v,u)\ge\rho/2\) in Theorem 2.1.

Snell's explicit premark regression (7.127ap)--(7.127ar) additionally has
unit curl, unit premark TV, a sure marked atom, and zero prescribed-payoff
change on the relevant source edge.  Its global minimum debt is zero, so it
correctly stops short of falsifying a theorem that essentially uses the full
positive-minimum hard residual.

## 11. The exact renewable part and the remaining adapter

Arm 2 of Theorem 9.1 has a natural clock candidate.  Let \(T\) be its first paid
disagreement date.  Then

\[
 T<m=\ell+1,
 \qquad\text{hence}\qquad T\le\ell.
 \tag{11.1}
\]

If the relevant convention marks the old paid row by \(\ell\), strict rank
descent is obtained when \(T<\ell\).  The remaining possibility \(T=\ell\)
is a genuine same-row paid return, but no checked interface consumes it merely
from that fact.  Thus the clock is nonincreasing, not yet a renewable finite
rank.  A chain which regenerates all hard-residual source fields at the new
paid edge cannot take the **strict** premark-payment subarm indefinitely.

Arm 3 is precisely where this argument stops.  It is an actual edge and its
large number has the correct source and target, but the mover is nearly
neutral.  The positive-minimum cap/debt identity can create a paid response
at its target, yet the first disagreement of that new response need not be
before \(m\).  It can therefore reset the clock rank.  Also, replacing the
premark strategy can erase rather than spend the old retained atom.  Neither
\(D_*>0\) nor (10.1) gives a signed atom-loss charge.

The smallest missing theorem is now the following source-attached statement.
At a near-minimum hard-residual source, every edge satisfying (9.3) must
produce one of:

1. a paid response at the target whose first disagreement is no later than
   the edge's premark disagreement;
2. an original-prefix-preserving reached block accepted by the checked
   positive-minimum two-cut consumer; or
3. an executable transition, not merely a sibling, to a fixed off-minimum
   debt collar.

Any of these outputs combines with Theorem 9.1 to pay the collar crossing or
give a renewable finite clock.  The existing cap/debt response chase proves
payment at the target in one branch but supplies none of the three chronology
clauses above.  This is the precise unresolved adapter; treating the TV seam
itself as a payoff collar would bypass it incorrectly.

## 12. Additional file inspected

* `notes/CODEX_SNELL__AGGREGATE_PAID_ORIENTATION_FINITE_ATOM_AND_NORMALIZED_PASSPORT.md`,
  especially Sections 7.18.7--7.18.10 and equations (7.127r)--(7.127as).

## 13. The canonical outer cap loop

The strict Fin4 minimum plateau gives a source-level test of the proposed
compact relation.  Let

\[
 X_*=(u_*,b_*)
\]

be the positive minimum pair, so

\[
 d_i=b_{*,i}-u_{*,i}\ge0,
 \qquad \sum_i d_i=D_*>0.
 \tag{13.1}
\]

The checked open debt-homotopy tube makes all Continue the unique exact root
against \(b_*\).  In particular, in the ordinary forward payoff/root
relation,

\[
 b_*\xrightarrow{\mathbf C}F(\mathbf C,b_*)=b_*
 \tag{13.2}
\]

is an exact Bellman self-loop with zero absorption.

At the same time, (13.1) gives

\[
 \|b_*-u_*\|_1=D_*,
 \qquad
 \|b_*-u_*\|_\infty\ge D_*/4.
 \tag{13.3}
\]

Thus the exact neutral recurrent point \(b_*\) lies in a fixed outer collar
around the minimum prescribed payoff \(u_*\).

### Proposition 13.1 (the outer loop is not an actual source transition)

The literal all-Continue prefix over a profile realizing or approximating the
semantic pair \((u_*,b_*)\) fixes that semantic pair.  It does not replace its
prescribed payoff \(u_*\) by the evaluation annotation \(b_*\).

Indeed
quittingTerminalSemanticPrefix_allContinue_eq_self_iff_isZeroNash_at_cap
says exactly that exact all-Continue Nash at the envelope \(b_*\) is
equivalent to

\[
 \operatorname{Prefix}_{\mathbf C}(u_*,b_*)=(u_*,b_*).
 \tag{13.4}
\]

The Bellman equality (13.2) lives in the finite-dimensional relation whose
tail is the payoff vector \(b_*\).  The literal source equality (13.4) lives
in the terminal-semantic relation whose prescribed coordinate is \(u_*\).
Identifying the two would erase the nonzero debt vector (13.1).

Consequently ordinary chain recurrence in the compact payoff/root relation
can always see the outer neutral loop without producing either positive
charge or an actual return from the outer annotation to the near-minimum
source.  This uses the positive minimum rather than a zero-debt local
regression: the separation (13.3) is macroscopic.

The same conclusion holds along the actual minimum-approaching sequence from
the strict plateau theorem.  Its envelopes converge to \(b_*\); eventually
all Continue is the unique exact cap root, and the literal prefixes keep the
actual semantic sources fixed.  Compactifying these two kinds of points does
not create the missing chronological arrow.

## 14. What genuine source-attached recurrence would prove

There is a simple exact positive theorem once recurrence occurs along one
literal orbit rather than in an untyped compact relation.

### Theorem 14.1 (uniformly charged actual returns)

Let \((C,d)\) be a compact metric state space, let \(E\) be a typed
chronological edge space with source and target maps, and let
\(q:E\to[0,\infty)\) be an additive edge charge.  Suppose there is one
composable infinite orbit

\[
 x_0\xrightarrow{e_0}x_1\xrightarrow{e_1}x_2\longrightarrow\cdots
 \tag{14.1}
\]

and restart times

\[
 0\le n_0<n_1<n_2<\cdots
\]

such that \(x_{n_k}\) belongs to one fixed compact set \(I\) and every
successive excursion pays

\[
 \sum_{n_k\le t<n_{k+1}}q(e_t)\ge q_0>0.
 \tag{14.2}
\]

Then, for every \(\varepsilon>0\) and \(Q>0\), there are \(k<\ell\) for which

\[
 d(x_{n_k},x_{n_\ell})<\varepsilon,
 \qquad
 \sum_{n_k\le t<n_\ell}q(e_t)\ge Q.
 \tag{14.3}
\]

### Proof

Cover \(I\) by \(N<\infty\) sets of diameter less than \(\varepsilon\).
Choose an integer \(L\) with \(Lq_0\ge Q\), and inspect \(NL+1\) restart
states.  One cover element contains at least \(L+1\) of them.  Its first and
last such visits are separated by at least \(L\) excursions, have distance
less than \(\varepsilon\), and (14.2) gives (14.3).  \(\square\)

For the approximate forward-packet question, the edges in (14.1) must carry
the literal Bellman successor, one fixed support-Nash tolerance, and the
punishment floor.  With those decoder fields, (14.3) is exactly the compact
charged near-return used to reverse a finite block into an approximate
periodic quitting profile.  The theorem therefore gives arbitrarily large
packet charge and hence the existing uniform-payoff consumer.

This is stronger than recurrence of a point or a chain component.  Every
successive row begins at the literal target of the preceding row, and every
restart state is reached on that same orbit.

## 15. The continuous Lyapunov alternative needs the same typing

Let \(P\subseteq E\) be a compact family of source-attached collar-crossing
edges.  Suppose a continuous \(L:C\to\mathbb R\) satisfies

\[
 L(s(e))\ge L(t(e))\quad(e\in E),
 \qquad
 L(s(e))>L(t(e))\quad(e\in P).
 \tag{15.1}
\]

Compactness of \(P\) and continuity give

\[
 \kappa:=\min_{e\in P}\bigl(L(s(e))-L(t(e))\bigr)>0.
 \tag{15.2}
\]

Hence one composable orbit contains at most

\[
 \frac{\max_C L-\min_C L}{\kappa}
 \tag{15.3}
\]

edges from \(P\).  If the hard residual forces another literal
source-attached \(P\)-edge after every terminal segment, (15.3) is a renewable
finite descent certificate.

The quantifier over **all** edges in (15.1) includes the source
reattachment/re-entry edges.  A Lyapunov function only for the formal
payoff/root Bellman relation does not telescope across a horizontal operation
which changes the outer annotation \(b\) back to the actual source payoff
\(u\).  Proposition 13.1 shows that this is exactly the current situation.

There is also no purely topological guarantee of a continuous
charge-dominating potential.  Proposition 79 in
CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md gives a compact closed
predecessor-serial relation with bounded total charge on every path but no
continuous function whose edge drop dominates that charge.  Conley's
continuous complete Lyapunov function, when available, only gives strict
order outside the chain-recurrent set; it need not pay charge quantitatively.
Equations (15.1)--(15.2) recover a fixed toll only after the relevant compact
edge family is proved disjoint from the neutral recurrent part.

## 16. Exact topological verdict

The desired topological dichotomy is valid after adding one of two substantive
game-facing hypotheses:

1. an actual composable source chronology with repeated uniformly charged
   returns to one compact inner set, as in Theorem 14.1; or
2. a compact actual edge system containing every source re-entry, together
   with a continuous Lyapunov function nonincreasing on all its edges and
   strict on the forced collar exits, as in Section 15.

Neither hypothesis follows from compactness or chain recurrence of the
approximate payoff/root relation.  The positive minimum instead supplies the
exact outer neutral loop (13.2), while literal source semantics supplies
(13.4).  The missing map \(b_*\rightsquigarrow u_*\) is not a Bellman edge.
Adding it to the graph by declaration creates an untyped recurrent cycle;
omitting it leaves recurrence stranded outside the actual source carrier.

Thus compact-relation recurrence is too weak for the requested globalization.
The new exact producer question is not topological:

> construct one literal source re-entry edge carrying the successor semantic
> pair, cap, law, and paid passport, or prove a Lyapunov inequality which also
> controls that re-entry.

Without this adapter, the linear seam certificate and the outer cap loop are
compatible and yield neither an approximate periodic packet nor a renewable
finite rank.

Additional sources inspected for this audit:

* UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean:
  quittingTerminalSemanticPrefix_allContinue_eq_self_iff_isZeroNash_at_cap;
* UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean;
* notes/CODEX_CEDAR__ERGODIC_NASH_BELLMAN_RECURRENCE.md;
* notes/CODEX_STRENGTHEN__FIN4_CAPACITY_POTENTIAL_STATIC_TOPOLOGY_SEPARATION.md;
* notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md, Proposition 79; and
* arch/CHRONOLOGICAL_OCCUPATION_DUALITY.md and
  arch/RECURRENCE_ARCHITECTURE_OBSTRUCTION.md.
