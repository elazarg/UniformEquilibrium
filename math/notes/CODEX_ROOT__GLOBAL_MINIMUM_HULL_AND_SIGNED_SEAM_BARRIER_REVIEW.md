# Global-minimum hull and signed seam barrier: initial review

Identity: CODEX_ROOT  
Date: 2026-08-31  
Status: two ordinary-mathematics statements appear sound; the global
counterexample interpretation needs qualification.

## Question reviewed

For a hypothetical four-player counterexample, can the law-tight saturation
hull at a global minimum be identified exactly, and can a non-all-Continue
exact root against an auxiliary continuation vector approach the minimum
without paying a fixed signed seam?

All caps and debts below use unrestricted behavioral unilateral deviations.

## 1. Exact global-minimum hull

Let (z_0=(p_0,mu)) belong to the joint semantic/law carrier, suppose
(D(p_0)=D_*>0), and suppose (D_*) is the global semantic-carrier minimum.
Then the proposed equality

\[
\operatorname{Sat}(z_0)=
\{(p,\mu)\text{ in the joint carrier}:D(p)=D_*\}
\tag{1}
\]

is correct for the checked definition of the law-tight cap--Nash saturation
hull.

For the forward inclusion, the right-hand set is closed, contains the origin,
and is same-law downward closed.  If an exact cap--Nash root prefixes a point
of debt (D_*), exact debt scaling and global minimality give

\[
D_*\le cD_*\le D_*,
\]

so (c=1).  A finite product root of joint Continue mass one is literally
all Continue, and its semantic/law prefix is the identity.  Hence the
right-hand set is invariant and contains the saturation hull.

For the reverse inclusion, the hull contains (z_0), and its checked
same-law closure inserts every carrier replacement of law (mu) and debt at
most (D(p_0)=D_*).  Global minimality turns that inequality into equality.

The complete law fixes the prescribed payoff by the reward-moment identity,
so this hull is a fixed-law cap fiber, not a nontrivial prefix orbit.

This is a useful exact characterization but not a new chamber consumer.  The
singleton/Never deletion and resulting full-debt/reset-rigid dichotomy are
already checked in
`finFour_noUniformPayoff_exists_lawTightGlobalMinimumMoatTwoChamber`.

## 2. Uniform signed seam barrier

The genuinely new candidate is the following quantitative statement.

Let (p=(U,B)) be a global minimum semantic pair for a hypothetical Fin4
counterexample, let

\[
D(p)=D_*>0,
\qquad
U_i-r_i(\{i\})\ge\delta>0
\quad(i\in\operatorname{Fin}4),
\]

and suppose all rewards have absolute value at most (R>0).  Let (V\le B)
coordinatewise, and let (x) be an exact quitting-root Nash profile against
(V).  If (x\ne\mathbf C), then

\[
\boxed{
\max_i(U_i-V_i)\ge
c_0:=\min\left\{\frac{D_*}{4},\frac\delta2,
                 \frac{\delta D_*}{96R}\right\}.}
\tag{2}
\]

### Proof audit

Put (d_i=B_i-U_i), (g_i=U_i-V_i), and
(arepsilon=\max_i g_i).  Since (V\le B), the auxiliary vector
(h=B-V=d+g) is coordinatewise nonnegative.  The checked theorem
`minimumTerminalSemantic_auxiliaryNash_budget` applies and gives

\[
D_*c(x)+\sum_i m_i(x)(D_*-d_i-g_i)\le0,
\tag{3}
\]

where (c(x)) is collision mass and (m_i(x)) singleton-(i) mass.

Choose (k) with maximal (d_k) and put
(	heta=D_*-d_k=\sum_{i\ne k}d_i).  Since every coefficient
(D_*-d_i) is at least (	heta), rearranging (3) shows

\[
\varepsilon\ge\theta.
\tag{4}
\]

If (arepsilon<D_*/4), (3) also gives

\[
c(x)+\sum_{i\ne k}m_i(x)\le\frac{2\varepsilon}{D_*}.
\tag{5}
\]

The left side is exactly the probability that at least one opponent of (k)
Quits.  Hence the sum of the three opponent Quit probabilities is at most
(6\varepsilon/D_*).

At all Continue, player (i)'s Quit-minus-Continue difference against (V)
is

\[
r_i(\{i\})-V_i\le-\delta+\varepsilon< -\delta/2.
\tag{6}
\]

If (x_k(Q)>0), exact Nash requires the corresponding difference at (x)
to be nonnegative.  The checked endpoint-product stability theorem, with
tail bound (2R), bounds the change by

\[
8R\cdot\frac{6\varepsilon}{D_*}.
\]

The tail bound is valid under the contradictory assumption
(arepsilon<c_0): from (V\le B\le R), (U\ge-R), and
(U_i-V_i\le\varepsilon\le R), one gets (|V_i|\le2R).  Thus

\[
\varepsilon\ge\frac{\delta D_*}{96R}.
\]

If (x_k(Q)=0), choose another active player.  Only two possibly active
opponents remain, giving the stronger denominator (64R); the stated
(96R) bound still follows.  Nontriviality guarantees an active player.
This completes (2).

The proof also handles proper debt faces, including a one-debtor vertex.
The already checked open auxiliary cube does not by itself give this
critical-face conclusion.

## 3. Exact scope of the barrier

Equation (2) proves the clean disjunction

\[
x\ne\mathbf C\text{ exact against }V
\Longrightarrow
\left(\exists i,\ V_i>B_i\right)
\ \lor\
\left(\exists i,\ U_i-V_i\ge c_0\right).
\tag{7}
\]

Only the second disjunct has a fixed quantitative floor in the proof above.
The first disjunct records an upward cap crossing, but its magnitude may be
arbitrarily small.  Therefore the slogan

> every nontrivial exact edge pays a macroscopic semantic seam

does not yet follow for unrestricted auxiliary continuations.  It is valid
for constructions known a priori to satisfy (V\le B).  Outside that order
interval one needs an additional robust-cap argument, or an accumulated seam
telescope with a supplied survival loss.

The checked signed semantic-seam telescope is conditional on a supplied
finite chain.  Its coercive inequality shows that a chain with a fixed
survival drop and minimum-debt endpoints must pay charge, absolute semantic
seam, or endpoint excess.  It does not itself construct an
extension-compatible chain and does not turn an arbitrarily small one-step
cap overshoot into a fixed toll.

## 4. Compact minimum-fiber consequences

If every coordinate debt is positive at every joint global minimum, compactness
does give a uniform positive debt-coordinate floor.  The closed set of
carrier points with some zero debt is then separated in total debt from the
minimum fiber by a fixed (Delta>0).  An exact prefix mapping a tail of debt
at least (D_*+\Delta) to debt (D_*) must have absorption at least

\[
\frac{\Delta}{D_*+\Delta}.
\]

This is sound but remains conditional on constructing renewable,
extension-compatible debt-kill/regeneration steps.

If some joint global minimum has a zero coordinate, applying the checked
strict classifier to a suitable positive-atom minimum law should recover the
reset-rigid alternative after the singleton/Never chamber is excluded.  The
adapter should be stated explicitly; it is not part of the signed-barrier
proof.

## 5. Unsupported extrapolations to avoid

The following claims are not established by the reviewed argument alone:

1. that every law-changing splice has a fixed seam floor;
2. that compact recurrence makes two such splices composable on one actual
   chronology;
3. that the resulting transition is a renewable finite-rank descent; or
4. that a recurrent reset machine must visit all four singleton owners.

For a law supported on one singleton ({j}) and Never, the calculation
((p-1)r_j(\{j\})>0) correctly forces (p<1) and
(r_j(\{j\})<0).  The reset chamber's distinct-owner conclusion should be
attributed to its positive opponent-incidence field, not to singleton cap
binding.

## Verdict

- Hull equality (1): correct, useful exact simplification, likely a short
  formalization.
- Singleton/Never deletion: already formalized; no new progress.
- Signed barrier (2): apparently correct and materially stronger than the
  existing open-cube statement; worthy of independent review and, if it
  passes, export.
- Macroscopic teleport-machine classification: useful heuristic, but not yet
  a theorem.  Extension-compatible source composition remains the missing
  consumer.

## Sources inspected

- `LawTightCapNashSaturationHull.lean`;
- `TerminalSemanticAuxiliaryNashBudget.lean`;
- `TerminalSemanticFinFourMinimumFiberIsolation.lean`;
- `Root/EndpointOpponentStability.lean`; and
- `Debt/Dynamic/TerminalSemanticSignedSeamTelescope.lean`.

## Next check

Independently falsify (2), paying special attention to negative (g_i), the
critical one-debtor face, and the (x_k(Q)=0) branch.  If it survives, package
the hull equality and signed barrier separately; only the latter should be
counted as conjecture-facing progress.
