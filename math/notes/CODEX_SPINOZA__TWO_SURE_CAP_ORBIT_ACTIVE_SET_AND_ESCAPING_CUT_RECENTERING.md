# Two-sure cap orbits stabilize their active set or recenter an escaping exact cap cut

Author: CODEX_SPINOZA

## Status

**Exact ordinary mathematics; orbit reduction, not Lean-checked and not a
terminal consumer.**  In the response-closed two-sure class, choose at every
node a full-gap exact cap response represented by a finite pure time.  The set
of players whose prescribed laws have become finite pure clocks grows
monotonically and stabilizes after at most two additions.  Thereafter all
unmoved spectator laws are literally fixed.

Every response edge has a first-disagreement cut with a fixed opponent-reach
floor.  If those cuts escape, fixed spectators acquire an actual joint Never
atom, and shifting at the cut produces a literal date-zero exact cap edge with
the same conditional gain and a distinct finite sure anchor.  This is stronger
than a weak moving-profile Never cylinder: the spectator laws are fixed along
the selected tail.  If the cuts stay bounded, the orbit remains a bounded-front
horizontal cap component; bounded front does not bound the later sure
deadlines or produce Nash--Bellman chronology.

The theorem isolates the exact projective residual.  It does not yet consume
the full-active case, where there are no fixed spectators, or the bounded-cut
case, where later clocks may still escape.

## 1. Input

Let \(I=\operatorname{Fin}4\), assume \(|r_i(S)|\le M\) with \(M>0\), and
assume a terminal exploitability gap \(\Gamma>0\).  Let

\[
 P_0\dashrightarrow_{i_0}P_1
 \dashrightarrow_{i_1}P_2\dashrightarrow\cdots
\tag{1}
\]

be a literal orbit such that:

1. every \(P_m\) has at least two distinct prescribed deterministic finite
   stopping clocks;
2. \(i_m\) satisfies \(d_{i_m}(P_m)\ge\Gamma\); and
3. \(P_{m+1}\) replaces only \(i_m\) by a deterministic finite pure time
   attaining its complete unrestricted cap.

The preceding exactification theorem produces exactly this orbit.

Let \(S_m\subseteq I\) be the players whose prescribed laws in \(P_m\) are
deterministic finite times.  If a player in \(S_m\) moves, it remains in
\(S_{m+1}\); if a player outside \(S_m\) moves, it enters.  Hence

\[
 S_m\subseteq S_{m+1},\qquad |S_m|\ge2.
\tag{2}
\]

After deleting a finite prefix, fix one set \(S\) with \(S_m=S\) for all
remaining \(m\).  Every mover belongs to \(S\), and every spectator law
\(P_{m,j}\), \(j\notin S\), is one fixed law \(\mu_j\), independent of
\(m\).

## 2. First-disagreement reach floor

Write \(T_{m,i_m}\) and \(T'_{m,i_m}\) for the mover's old and new finite
times and put

\[
 r_m=\min\{T_{m,i_m},T'_{m,i_m}\}.
\tag{3}
\]

The two pure clocks agree strictly before \(r_m\) and take different actions
at \(r_m\).  Pure-time first-disagreement factorization gives

\[
 U_{i_m}(P_{m+1})-U_{i_m}(P_m)
 =L_m G_m,
\tag{4}
\]

where

\[
 L_m=\Pr_{P_m}(T_j\ge r_m\text{ for every }j\ne i_m)
\tag{5}
\]

and \(|G_m|\le2M\).  Since the left side is at least \(\Gamma\),

\[
 L_m\ge\kappa:=\min\{1,\Gamma/(2M)\}>0.
\tag{6}
\]

In particular every other active pure clock satisfies

\[
 T_{m,j}\ge r_m\qquad(j\in S\setminus\{i_m\}),
\tag{7}
\]

because otherwise the edge is screened and has zero gain.

After a subsequence fix the mover \(i\), the direction of the toggle at the
cut, and whether the cut sequence is bounded or tends to infinity.

## 3. Escaping cuts give fixed-spectator cemetery mass

Assume \(r_m\to\infty\).  Since the spectator laws are fixed after active-set
stabilization, (5)--(7) imply

\[
 \prod_{j\notin S}\mu_j([r_m,\mathrm{Never}])\ge\kappa.
\tag{8}
\]

Letting \(m\to\infty\) gives the exact actual-law conclusion

\[
 \boxed{
 \prod_{j\notin S}\mu_j(\{\mathrm{Never}\})\ge\kappa.}
\tag{9}
\]

For \(S=I\), (9) is the empty-product tautology and supplies no cemetery
information.  For every proper active set it gives positive Never mass for
each fixed spectator, and their joint spectator-Never event has probability
at least \(\kappa\).

This is not obtained by taking weak limits of moving spectator laws: the laws
in (9) are literally the unchanged laws already present at every orbit node.

## 4. Literal cut recentering preserves exact cap attainment

Let

\[
 A_m=\operatorname{Shift}_{r_m}P_m,qquad
 B_m=\operatorname{Shift}_{r_m}P_{m+1}
\tag{10}
\]

be the actual conditional suffix profiles at the first disagreement.  The
two full profiles agree before the cut, and the mover's replacement was a
complete cap response.  Therefore

\[
 B_m=A_m[i\leftarrow b_{m,i}]
\tag{11}
\]

literally, \(b_{m,i}\) attains player \(i\)'s complete cap at \(A_m\), and

\[
 U_i(B_m)-U_i(A_m)=G_m\ge\Gamma.
\tag{12}
\]

Indeed, any behavioral deviation at \(A_m\) lifts to a deviation at \(P_m\)
which copies the prescribed mover law before \(r_m\).  Its full improvement
over the prescribed source is \(L_m\) times its suffix improvement.  If it
beat \(b_{m,i}\) at the suffix, its lift would beat the cap-attaining response
at \(P_m\), a contradiction.  Equation (4) then gives (12).

At date zero of the recentered pair, one of the old/new mover clocks Quits
surely and the other Continues.  By (7), every other active player remains a
deterministic finite sure clock in the suffix, at time
\(T_{m,j}-r_m\).  Thus (10)--(12) are a literal date-zero exact-cap toggle
with a distinct finite sure anchor, not merely a semantic paid port.

## 5. Exhaustive clock-position reduction

Every selected response-closed two-sure orbit therefore has, after finite
active-set stabilization and subselection, one of the following outputs:

\[
\boxed{
\begin{array}{ll}
\textbf{bounded cut:}& r_m=r\text{ is fixed, giving a fixed-front exact-cap}\
&\text{toggle component whose later sure deadlines may still escape};\\[1mm]
\textbf{escaping cut:}& r_m\to\infty, giving the recentered date-zero exact}\
&\text{cap source (10)--(12), plus the actual fixed-spectator}\
&\text{Never cylinder (9) whenever }S\ne I.
\end{array}}
\tag{13}
\]

The escaping branch is source-faithful: the new source is the literal suffix
at the first disagreement of one exact cap edge, and the target is its literal
cap child.  It is not a Nash--Bellman edge.

## 6. Consumer audit

The theorem removes one false compactification: after active-set
stabilization, escaping cuts do not merely give a weak Never atom of moving
laws.  Every nonactive player's law is fixed, so the cemetery product in (9)
is actual and quantitative.

It still stops short in two exact cases.

1. If \(S=I\), every player has already become a pure finite clock and there
   is no fixed spectator to carry (9).  The vector of relative active
   deadlines can escape without a smaller player set.
2. If the cuts are bounded, an edge keeps toggling at a fixed front date but
   the distinct sure anchor can move arbitrarily far into the suffix.  This is
   not a compact finite response cycle unless those relative deadlines are
   also tight.

Even when (9) is nontrivial, the current finite-splice consumer needs a Never
factor on a specifically moved law together with its matching deleted
survival packet.  Here the cemetery mass belongs to fixed spectators, whereas
the moved player lies in \(S\) and uses a finite pure cap.  Thus (9) does not
by itself satisfy that consumer's product.  This mismatch is the remaining
adapter, not lack of an actual tail law.

## Sources inspected

- `notes/CODEX_SPINOZA__RECENTERED_PAID_TAIL_EXACTIFIES_TO_TWO_SURE_RESPONSE_ORBIT.md`;
- `notes/CODEX_HAHN__TWO_RENEWED_SURE_CLOCKS_GIVE_FINITE_COMPLETE_SEMANTICS.md`;
- `notes/CODEX_GROMOV__TWO_SURE_CLOCK_FINITE_RESPONSE_CYCLE_NOGO.md`;
- `exports/FINITE_CLOCK_DOUBLE_FULL_GAP_COSOURCE.md`;
- `formalized/CAP_SWITCH_RECTANGLE_FULL_CHORD_AND_FINITE_SPLICE_BOUNDARY.md`;
- `UniformEquilibrium/Quitting/Paths/SurvivalWeightedSuffixRegret.lean`; and
- `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`.

## Boundary and nonclaims

- The monotone active set records syntactic deterministic finite clocks, not
  zero-debt coordinates.  Horizontal responses may reactivate old debts.
- The fixed spectator laws arise only after the active set stabilizes.  No
  claim is made about earlier changing laws.
- The reach floor is full opponent survival to the inclusive
  first-disagreement cut.  It is not joint survival beyond the cut.
- Recentered cap optimality uses the original exact cap attainment, not only
  the lower bound on its gain.
- No exact root, Nash--Bellman block, terminal approximate Nash profile,
  source return, or uniform-equilibrium payoff is produced.

## Next exact question

Can the actual spectator-Never cylinder in the proper-active escaping branch
be transferred to the moved cap law without losing the exact date-zero source
edge, or can the full-active relative-deadline vector be forced into a bounded
order-type component by the positive global minimum?  Either result would
turn (13) into a genuine terminal consumer rather than a sharper projective
boundary.
